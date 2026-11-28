/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly1Base
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Sort/Combine WP (`Arisca.Proof.Poly1Sort`)

`XPost`-polymorphic `Mem 64` WP proof for `ar_sort_combine` (`ar_sort_combine_wp`).
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

/-! ## 1. `ar_sort_combine_wp` (`Arisca.Src.Poly`) -/

private theorem CombineInv.start {nOut : Nat} {srcPool qm : List (BitVec 32)}
    {ql qh : List (BitVec 64)} {aArr : List (BitVec 32)} {qn : Nat}
    {qlPtr qhPtr ixPtr : BitVec 64} {Rcmb : Mem 64 → Prop} {m : Mem 64}
    (hperm : PermN aArr qn)
    (hm : (array64 qlPtr ql ⋆ array64 qhPtr qh ⋆ array (t := i32) ixPtr aArr ⋆ Rcmb) m) :
    CombineInv nOut srcPool qm ql qh aArr qn qlPtr qhPtr ixPtr Rcmb 0 0 m :=
  ⟨ql, qh, aArr, rfl, rfl, rfl, Nat.zero_le _, Nat.zero_le _,
    fun _ hp => by omega, fun _ _ _ => rfl, by simp, fun _ hp => by omega,
    fun _ _ => ⟨rfl, rfl⟩, (fun σ => by
      have h1 : polyEvalIdxOf nOut σ srcPool qm ql qh aArr 0 qn =
          ((List.range qn).map (fun k => (aArr.getD k 0#32).toNat)).foldl
            (fun acc idx => acc + termEval nOut σ srcPool qm ql qh idx) 0#nOut := by
        simp [polyEvalIdxOf, List.foldl_map]
      have h2 : polyEval nOut σ srcPool qm ql qh qn =
          (List.range qn).foldl
            (fun acc idx => acc + termEval nOut σ srcPool qm ql qh idx) 0#nOut := by
        simp [polyEval, polyEvalRange]
      simp only [polyEvalIdxOf_nil, Nat.sub_zero, BitVec.zero_add]
      rw [h1, h2]; exact foldl_add_perm _ hperm), hm⟩

private theorem bv64_zext32_toNat (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans x.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

private theorem merge_lo2w_toNat {lo w : BitVec 64} (h64b : lo.toNat + 2 * w.toNat < 2 ^ 64) :
    (lo + 2#64 * w).toNat = lo.toNat + 2 * w.toNat := by
  have hw_bd : w.toNat < 2 ^ 63 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_mul, show (2#64 : BitVec 64).toNat = 2 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * w.toNat < 2 ^ 64), Nat.mod_eq_of_lt h64b]

private def MergeWInv (s : ArCtxState) (ix ix2 : List (BitVec 32))
    (Rmerge : Mem 64 → Prop) (wrem : Nat) (xs : Tup Val [i64, i64, i64])
    (mW : Mem 64) : Prop :=
  let (aPtr, bPtr, w, _) := xs
  ∃ aArr bArr : List (BitVec 32),
    ((aPtr = s.ix ∧ bPtr = s.ix2 ∧ aArr.length = ix.length ∧ bArr.length = ix2.length) ∨
     (aPtr = s.ix2 ∧ bPtr = s.ix ∧ aArr.length = ix2.length ∧ bArr.length = ix.length)) ∧
    PermN aArr s.qn.toNat ∧ 16 ≤ w.toNat ∧ w.toNat ≤ 2 * max 16 s.qn.toNat ∧
    wrem = 2 * max 16 s.qn.toNat - w.toNat ∧
    (array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bArr ⋆ Rmerge) mW

private def MergeLoInv (aPtr bPtr : BitVec 64) (aArr bArr : List (BitVec 32)) (qn : Nat)
    (w : BitVec 64) (Rmerge : Mem 64 → Prop) (lorem : Nat) (xs : Tup Val [i64])
    (mL : Mem 64) : Prop :=
  let (lo, _) := xs
  ∃ bCur : List (BitVec 32),
    bCur.length = bArr.length ∧ lo.toNat ≤ qn + 2 * w.toNat ∧
    lorem = (qn + 2 * w.toNat) - lo.toNat ∧
    ((List.range (min lo.toNat qn)).map (fun t => (bCur.getD t 0#32).toNat)).Perm
      ((List.range (min lo.toNat qn)).map (fun t => (aArr.getD t 0#32).toNat)) ∧
    (array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bCur ⋆ Rmerge) mL

private def MergePInv (aPtr bPtr : BitVec 64) (aArr bArr bCur : List (BitVec 32))
    (lo mid hi q : Nat) (Rmerge : Mem 64 → Prop) (prem : Nat) (xs : Tup Val [i32, i32])
    (mP : Mem 64) : Prop :=
  let (p1, o1, _) := xs
  prem = mid - p1.toNat ∧
  MergeChunkInv aPtr bPtr aArr bArr bCur lo mid hi p1.toNat q o1.toNat Rmerge mP

private def MergeQInv (aPtr bPtr : BitVec 64) (aArr bArr bCur : List (BitVec 32))
    (lo mid hi : Nat) (Rmerge : Mem 64 → Prop) (qrem : Nat) (xs : Tup Val [i32, i32])
    (mQ : Mem 64) : Prop :=
  let (q1, o2, _) := xs
  qrem = hi - q1.toNat ∧
  MergeChunkInv aPtr bPtr aArr bArr bCur lo mid hi mid q1.toNat o2.toNat Rmerge mQ

private def CombineJInv (nOut qn i : Nat) (srcPool qm : List (BitVec 32))
    (ql qh : List (BitVec 64)) (aArr : List (BitVec 32)) (h0 : BitVec 32)
    (mC : Mem 64) (jrem : Nat) (xs : Tup Val [i64, i64, i32]) (mJ : Mem 64) : Prop :=
  let (l, h, j, _) := xs
  mJ = mC ∧ i + 1 ≤ j.toNat ∧ j.toNat ≤ qn ∧ jrem = qn - j.toNat ∧
  (∀ σ : Nat → Bool,
    (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
      then coeff128 nOut l h else 0#nOut) +
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr j.toNat (qn - j.toNat) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i (qn - i))

private theorem combine_cadd_coeff {nOut : Nat} {ql qlC qh qhC : List (BitVec 64)}
    {aArr aC : List (BitVec 32)} {l h nl nh : BitVec 64} {j : Nat} {hj_aC : j < aC.length}
    (haj_ql : (aC[j]'hj_aC).toNat < qlC.length) (haj_qh : (aC[j]'hj_aC).toNat < qhC.length)
    (haj_eq : aC[j]'hj_aC = aArr.getD j 0#32)
    (haj_unmod : qlC.getD (aArr.getD j 0#32).toNat 0#64 = ql.getD (aArr.getD j 0#32).toNat 0#64 ∧
      qhC.getD (aArr.getD j 0#32).toNat 0#64 = qh.getD (aArr.getD j 0#32).toNat 0#64)
    (hcadd : coeff128 nOut nl nh = coeff128 nOut l h +
      coeff128 nOut (qlC[(aC[j]'hj_aC).toNat]'haj_ql) (qhC[(aC[j]'hj_aC).toNat]'haj_qh)) :
    coeff128 nOut nl nh = coeff128 nOut l h +
      coeff128 nOut (ql.getD (aArr.getD j 0#32).toNat 0#64)
        (qh.getD (aArr.getD j 0#32).toNat 0#64) := by
  rw [hcadd, ← getD_eq_getElem qlC 0#64 haj_ql, ← getD_eq_getElem qhC 0#64 haj_qh,
    haj_eq, haj_unmod.1, haj_unmod.2]

private theorem sort_combine_ret_mem {cx : BitVec 64} {s sMid : ArCtxState}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs qlC qhC : List (BitVec 64)}
    {ix ix2 aArr bArr aC bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {aPtr bPtr : BitVec 64} {restTQ R : Mem 64 → Prop} {mC : Mem 64}
    (hsMid : sMid = { s with ix := aPtr, ix2 := bPtr })
    (haC_len : aC.length = aArr.length)
    (hptrs : (aPtr = s.ix ∧ bPtr = s.ix2 ∧ aArr.length = ix.length ∧ bArr.length = ix2.length) ∨
      (aPtr = s.ix2 ∧ bPtr = s.ix ∧ aArr.length = ix2.length ∧ bArr.length = ix.length))
    (hfoc : ∀ (s' : ArCtxState) (ql' qh' : List (BitVec 64)) (ix' ix2' : List (BitVec 32)),
      s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
      s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh → s'.bx = s.bx →
      s'.vq_off = s.vq_off → s'.vq = s.vq → s'.vq_skip = s.vq_skip →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧ ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧ ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s' qm qs ql' qh' ix' ix2' bx vqOff vq vqSkip =
        array (t := i32) (s.pool.getD s.pc.toNat 0#64) (if s.pc.toNat = 0 then pool0 else pool1) ⋆
        array (t := i32) s.qm qm ⋆ array64 s.ql ql' ⋆ array64 s.qh qh' ⋆
        array (t := i32) s'.ix ix' ⋆ array (t := i32) s'.ix2 ix2' ⋆ restTQ)
    (hmC : (array64 s.ql qlC ⋆ array64 s.qh qhC ⋆ array (t := i32) sMid.ix aC ⋆
      (arCtxMem cx sMid ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64)
        (if s.pc.toNat = 0 then pool0 else pool1) ⋆
        array (t := i32) s.qm qm ⋆ array (t := i32) sMid.ix2 bArr ⋆ (restTQ ⋆ R))) mC) :
    (arCtxMem cx sMid ⋆ tMem sMid tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem sMid qm qs qlC qhC aC bArr bx vqOff vq vqSkip ⋆ R) mC := by
  have h1 : sMid.tm = s.tm := by rw [hsMid]
  have h2 : sMid.ts = s.ts := by rw [hsMid]
  have h3 : sMid.tl = s.tl := by rw [hsMid]
  have h4 : sMid.th = s.th := by rw [hsMid]
  have h5 : sMid.pool = s.pool := by rw [hsMid]
  have h6 : sMid.qm = s.qm := by rw [hsMid]
  have h7 : sMid.qs = s.qs := by rw [hsMid]
  have h8 : sMid.ql = s.ql := by rw [hsMid]
  have h9 : sMid.qh = s.qh := by rw [hsMid]
  have h10 : sMid.bx = s.bx := by rw [hsMid]
  have h11 : sMid.vq_off = s.vq_off := by rw [hsMid]
  have h12 : sMid.vq = s.vq := by rw [hsMid]
  have h13 : sMid.vq_skip = s.vq_skip := by rw [hsMid]
  have hfoc' := hfoc sMid qlC qhC aC bArr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 (by
    rw [hsMid]
    rcases hptrs with ⟨ha, hb, hal, hbl⟩ | ⟨ha, hb, hal, hbl⟩
    · left; exact ⟨ha, hb, by omega, by omega⟩
    · right; exact ⟨ha, hb, by omega, by omega⟩)
  suffices h : ((tMem sMid tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
      qMem sMid qm qs qlC qhC aC bArr bx vqOff vq vqSkip) ⋆
      (arCtxMem cx sMid ⋆ R)) mC from sep_cast h (by ac_rfl)
  rw [hfoc']; exact sep_cast hmC (by ac_rfl)

private theorem sort_combine_init_step {a1 : List (BitVec 32)} {i : BitVec 32}
    (ha1_id : ∀ t < i.toNat, (a1.getD t 0#32).toNat = t) (hi_ix : i.toNat < a1.length) :
    ∀ t < i.toNat + 1, ((a1.set i.toNat i).getD t 0#32).toNat = t := by
  intro t ht; rw [getD_set_eq a1 0#32 i hi_ix]
  by_cases hti : t = i.toNat
  · subst hti; simp
  · simp only [hti, ↓reduceIte]; exact ha1_id t (by omega)

private def InsBlockInv (s : ArCtxState) (ix : List (BitVec 32))
    (Rix : Mem 64 → Prop) (irem : Nat) (xs : Tup Val [i32]) (m2 : Mem 64) : Prop :=
  let (i2, _) := xs
  ∃ a2 : List (BitVec 32), a2.length = ix.length ∧ PermN a2 s.qn.toNat ∧
    irem = s.qn.toNat - min i2.toNat s.qn.toNat ∧ i2.toNat < s.qn.toNat + 16 ∧
    (array (t := i32) s.ix a2 ⋆ Rix) m2

private def InsJInv (s : ArCtxState) (ix : List (BitVec 32)) (i2 e : BitVec 32)
    (Rix : Mem 64 → Prop) (jrem : Nat) (xs : Tup Val [i32]) (m3 : Mem 64) : Prop :=
  let (j2, _) := xs
  ∃ a3 : List (BitVec 32), a3.length = ix.length ∧ PermN a3 s.qn.toNat ∧
    i2.toNat + 1 ≤ j2.toNat ∧ j2.toNat ≤ e.toNat + 1 ∧
    jrem = (e.toNat + 1) - min j2.toNat (e.toNat + 1) ∧ (array (t := i32) s.ix a3 ⋆ Rix) m3

private def InsQInv (s : ArCtxState) (ix : List (BitVec 32)) (i2 j2 x : BitVec 32)
    (Rix : Mem 64 → Prop) (qrem : Nat) (xs : Tup Val [i32]) (m4 : Mem 64) : Prop :=
  let (q2, _) := xs
  ∃ a4 : List (BitVec 32), a4.length = ix.length ∧ i2.toNat ≤ q2.toNat ∧
    q2.toNat ≤ j2.toNat ∧ qrem = q2.toNat ∧ PermN (a4.set q2.toNat x) s.qn.toNat ∧
    (array (t := i32) s.ix a4 ⋆ Rix) m4

private def MergeChunkLoopInv (aPtr bPtr : BitVec 64) (aArr bArr bCur : List (BitVec 32))
    (lo mid hi : Nat) (Rmerge : Mem 64 → Prop) (pqrem : Nat) (xs : Tup Val [i32, i32, i32])
    (mM : Mem 64) : Prop :=
  let (p, q, o, _) := xs
  pqrem = (hi - lo) - (o.toNat - lo) ∧
  MergeChunkInv aPtr bPtr aArr bArr bCur lo mid hi p.toNat q.toNat o.toNat Rmerge mM

private def CombineLoopInv (nOut qn : Nat) (srcPool qm : List (BitVec 32))
    (ql qh : List (BitVec 64)) (aArr : List (BitVec 32)) (qlPtr qhPtr ixPtr : BitVec 64)
    (Rcmb : Mem 64 → Prop) (irem : Nat) (xs : Tup Val [i32, i32]) (mC : Mem 64) : Prop :=
  let (i, k, _) := xs
  irem = qn - i.toNat ∧
  CombineInv nOut srcPool qm ql qh aArr qn qlPtr qhPtr ixPtr Rcmb k.toNat i.toNat mC

private theorem sort_combine_vqm1_lt {a4 : List (BitVec 32)} {q2 x : BitVec 32} {qn : Nat}
    (hq_lt : q2.toNat < a4.length) (hqm1_lt : q2.toNat - 1 < a4.length) (hq_pos : 1 ≤ q2.toNat)
    (hperm4 : PermN (a4.set q2.toNat x) qn) (hhi : q2.toNat ≤ qn) :
    (a4[q2.toNat - 1]'hqm1_lt).toNat < qn := by
  have hv_eq : a4[q2.toNat - 1]'hqm1_lt = a4.getD (q2.toNat - 1) 0#32 := by
    rw [getD_eq_getElem a4 0#32 hqm1_lt]
  have hget : ((a4.set q2.toNat x).getD (q2.toNat - 1) 0#32).toNat =
      (a4[q2.toNat - 1]'hqm1_lt).toNat := by
    rw [getD_set_eq a4 0#32 x hq_lt]
    simp only [show q2.toNat - 1 ≠ q2.toNat by omega, ↓reduceIte, hv_eq]
  rw [← hget]; exact hperm4.mem_lt (by omega)

private def SortInitInv (s : ArCtxState) (ix : List (BitVec 32)) (Rix : Mem 64 → Prop)
    (rem : Nat) (xs : Tup Val [i32]) (m1 : Mem 64) : Prop :=
  let (i, _) := xs
  ∃ a1 : List (BitVec 32), a1.length = ix.length ∧ i.toNat ≤ s.qn.toNat ∧
    rem = s.qn.toNat - i.toNat ∧ (∀ t < i.toNat, (a1.getD t 0#32).toNat = t) ∧
    (array (t := i32) s.ix a1 ⋆ Rix) m1

private theorem sort_combine_w_next {s : ArCtxState} {aPtr bPtr : BitVec 64} {w lo : BitVec 64}
    {ix ix2 aArr bArr bCur : List (BitVec 32)} {Rmerge : Mem 64 → Prop} {mL : Mem 64}
    (hptrs : (aPtr = s.ix ∧ bPtr = s.ix2 ∧ aArr.length = ix.length ∧ bArr.length = ix2.length) ∨
      (aPtr = s.ix2 ∧ bPtr = s.ix ∧ aArr.length = ix2.length ∧ bArr.length = ix.length))
    (hpermA : PermN aArr s.qn.toNat) (hb_len : bCur.length = bArr.length)
    (hlo_ge : s.qn.toNat ≤ lo.toNat)
    (hprevL : ((List.range (min lo.toNat s.qn.toNat)).map
      (fun t => (bCur.getD t 0#32).toNat)).Perm
      ((List.range (min lo.toNat s.qn.toNat)).map (fun t => (aArr.getD t 0#32).toNat)))
    (hw_lo : 16 ≤ w.toNat) (hw_shl : (w <<< 1#64).toNat = 2 * w.toNat)
    (hw2_bd : (w <<< 1#64).toNat ≤ 2 * max 16 s.qn.toNat)
    (hmL : (array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bCur ⋆ Rmerge) mL) :
    MergeWInv s ix ix2 Rmerge (2 * max 16 s.qn.toNat - (w <<< 1#64).toNat)
      (bPtr, aPtr, w <<< 1#64, ⟨⟩) mL := by
  have hpermB : PermN bCur s.qn.toNat := by
    rw [Nat.min_eq_right hlo_ge] at hprevL; exact hprevL.trans hpermA
  refine ⟨bCur, aArr, ?_, hpermB, by rw [hw_shl]; omega, hw2_bd, rfl, sep_cast hmL (by ac_rfl)⟩
  rcases hptrs with ⟨ha, hb, hal, hbl⟩ | ⟨ha, hb, hal, hbl⟩ <;> simp [ha, hb, hal, hbl, hb_len]

private theorem sort_combine_lo_next {aPtr bPtr : BitVec 64} {w lo : BitVec 64}
    {aArr bArr bCur bQ : List (BitVec 32)} {midNat hiNat qn : Nat}
    {Rmerge : Mem 64 → Prop} {mQ : Mem 64}
    (hbQ_len : bQ.length = bArr.length) (h64b : lo.toNat + 2 * w.toNat < 2 ^ 64)
    (hlo_mid : lo.toNat ≤ midNat) (hmid_hi : midNat ≤ hiNat) (hhi_qn : hiNat ≤ qn)
    (hhi_v : hiNat = min (lo.toNat + 2 * w.toNat) qn)
    (hprevL : ((List.range (min lo.toNat qn)).map (fun t => (bCur.getD t 0#32).toNat)).Perm
      ((List.range (min lo.toNat qn)).map (fun t => (aArr.getD t 0#32).toNat)))
    (hkeepQ : ∀ t < lo.toNat, bQ.getD t 0#32 = bCur.getD t 0#32)
    (hpermQ : ((List.range (hiNat - lo.toNat)).map
        (fun t => (bQ.getD (lo.toNat + t) 0#32).toNat)).Perm
      ((List.range (hiNat - lo.toNat)).map (fun t => (aArr.getD (lo.toNat + t) 0#32).toNat)))
    (hmQ : (array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bQ ⋆ Rmerge) mQ) :
    MergeLoInv aPtr bPtr aArr bArr qn w Rmerge
      ((qn + 2 * w.toNat) - (lo + 2#64 * w).toNat) (lo + 2#64 * w, ⟨⟩) mQ := by
  have hlo2w := merge_lo2w_toNat h64b
  refine ⟨bQ, hbQ_len, by rw [hlo2w]; omega, rfl, ?_, hmQ⟩
  rw [hlo2w]
  exact merge_lo_next_perm (mid := midNat) (le_trans hlo_mid hmid_hi) (by omega) hhi_v hprevL
    hkeepQ (by simpa [Nat.sub_self] using hpermQ)

private theorem sort_combine_ins_next {s : ArCtxState} {ix : List (BitVec 32)}
    {i2 j2 q2 : BitVec 32} {x : BitVec 32} {a4 : List (BitVec 32)}
    {Rix : Mem 64 → Prop} {m' : Mem 64}
    (ha4_len : a4.length = ix.length) (hqn_ix : s.qn.toNat ≤ ix.length)
    (hj_qn : j2.toNat < s.qn.toNat) (hq_j : q2.toNat ≤ j2.toNat) (hq_gt : i2.toNat < q2.toNat)
    (hperm4 : PermN (a4.set q2.toNat x) s.qn.toNat)
    (hm' : (array (t := i32) s.ix (a4.set q2.toNat (a4[q2.toNat - 1]'(by omega))) ⋆ Rix) m') :
    InsQInv s ix i2 j2 x Rix (q2.toNat - 1) (q2 - 1#32, ⟨⟩) m' := by
  have hqm1 : (q2 - 1#32).toNat = q2.toNat - 1 := by c0_bv_omega [hq_gt]
  have hqm1_lt : q2.toNat - 1 < a4.length := by omega
  have hv_eq : a4[q2.toNat - 1]'hqm1_lt = a4.getD (q2.toNat - 1) 0#32 :=
    (getD_eq_getElem a4 0#32 hqm1_lt).symm
  refine ⟨_, by simp [ha4_len], by omega, by omega, hqm1.symm, ?_, hm'⟩
  rw [hqm1]; exact hperm4.insert_shift (by omega) (by omega) (by omega) hv_eq

private theorem sort_combine_ins_hi {qn i2 : BitVec 32} {b : Bool}
    (hsub : (qn - i2).toNat = qn.toNat - i2.toNat)
    (hb : CmpOp.ult.evalBits (qn - i2) 16#32 = b) :
    if b then qn.toNat = min (i2.toNat + 16) qn.toNat
    else ¬ qn.toNat - i2.toNat < 16 := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hlt : ¬ (qn - i2) < 16#32 := of_decide_eq_false hb
    rw [BitVec.lt_def, hsub] at hlt; exact hlt
  · simp only [↓reduceIte]
    have hlt : (qn - i2) < 16#32 := of_decide_eq_true hb
    rw [BitVec.lt_def, hsub] at hlt
    change qn.toNat - i2.toNat < 16 at hlt; omega

private theorem sort_combine_jm_step_p {aPtr bPtr : BitVec 64}
    {aArr bArr bCur bM : List (BitVec 32)}
    {lo mid hi : Nat} {p q o : BitVec 32} {Rmerge : Mem 64 → Prop} {m' : Mem 64}
    (hbM_len : bM.length = bArr.length) (hlo_p : lo ≤ p.toNat) (hp_lt : p.toNat < mid)
    (hmid_q : mid ≤ q.toNat) (hq_hi : q.toNat ≤ hi)
    (ho_eq : o.toNat = lo + (p.toNat - lo) + (q.toNat - mid)) (ho_lt : o.toNat < bM.length)
    (hp_a : p.toNat < aArr.length) (hkeepM : ∀ t < lo, bM.getD t 0#32 = bCur.getD t 0#32)
    (hpermM : ((List.range (o.toNat - lo)).map (fun t => (bM.getD (lo + t) 0#32).toNat) ++
        (List.range (mid - p.toNat)).map (fun t => (aArr.getD (p.toNat + t) 0#32).toNat) ++
        (List.range (hi - q.toNat)).map (fun t => (aArr.getD (q.toNat + t) 0#32).toNat)).Perm
        ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat)))
    (ho_p1 : (o + 1#32).toNat = o.toNat + 1) (hp_p1 : (p + 1#32).toNat = p.toNat + 1)
    (hm' : (array (t := i32) aPtr aArr ⋆
      array (t := i32) bPtr (bM.set o.toNat (aArr[p.toNat]'hp_a)) ⋆ Rmerge) m') :
    MergeChunkLoopInv aPtr bPtr aArr bArr bCur lo mid hi Rmerge
      ((hi - lo) - ((o + 1#32).toNat - lo)) (p + 1#32, q, o + 1#32, ⟨⟩) m' := by
  refine ⟨rfl, ?_⟩
  rw [ho_p1, hp_p1]
  exact MergeChunkInv.step_p hbM_len hlo_p hp_lt hmid_q hq_hi ho_eq ho_lt hp_a hkeepM hpermM hm'

private theorem sort_combine_jm_step_q {aPtr bPtr : BitVec 64}
    {aArr bArr bCur bM : List (BitVec 32)}
    {lo mid hi : Nat} {p q o : BitVec 32} {Rmerge : Mem 64 → Prop} {m' : Mem 64}
    (hbM_len : bM.length = bArr.length) (hlo_p : lo ≤ p.toNat) (hp_mid : p.toNat ≤ mid)
    (hmid_q : mid ≤ q.toNat) (hq_lt : q.toNat < hi)
    (ho_eq : o.toNat = lo + (p.toNat - lo) + (q.toNat - mid)) (ho_lt : o.toNat < bM.length)
    (hq_a : q.toNat < aArr.length) (hkeepM : ∀ t < lo, bM.getD t 0#32 = bCur.getD t 0#32)
    (hpermM : ((List.range (o.toNat - lo)).map (fun t => (bM.getD (lo + t) 0#32).toNat) ++
        (List.range (mid - p.toNat)).map (fun t => (aArr.getD (p.toNat + t) 0#32).toNat) ++
        (List.range (hi - q.toNat)).map (fun t => (aArr.getD (q.toNat + t) 0#32).toNat)).Perm
        ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat)))
    (ho_p1 : (o + 1#32).toNat = o.toNat + 1) (hq_p1 : (q + 1#32).toNat = q.toNat + 1)
    (hm' : (array (t := i32) aPtr aArr ⋆
      array (t := i32) bPtr (bM.set o.toNat (aArr[q.toNat]'hq_a)) ⋆ Rmerge) m') :
    MergeChunkLoopInv aPtr bPtr aArr bArr bCur lo mid hi Rmerge
      ((hi - lo) - ((o + 1#32).toNat - lo)) (p, q + 1#32, o + 1#32, ⟨⟩) m' := by
  refine ⟨rfl, ?_⟩
  rw [ho_p1, hq_p1]
  exact MergeChunkInv.step_q hbM_len hlo_p hp_mid hmid_q hq_lt ho_eq ho_lt hq_a hkeepM hpermM hm'

private theorem sort_combine_jp_next {aPtr bPtr : BitVec 64}
    {aArr bArr bCur bP : List (BitVec 32)}
    {lo mid hi qNat : Nat} {p1 o1 : BitVec 32} {Rmerge : Mem 64 → Prop} {m' : Mem 64}
    (hbP_len : bP.length = bArr.length) (hlo_p1 : lo ≤ p1.toNat) (hp1_lt : p1.toNat < mid)
    (hmid_q : mid ≤ qNat) (hq_hi : qNat ≤ hi)
    (ho1_eq : o1.toNat = lo + (p1.toNat - lo) + (qNat - mid)) (ho1_lt : o1.toNat < bP.length)
    (hp1_a : p1.toNat < aArr.length) (hkeepP : ∀ t < lo, bP.getD t 0#32 = bCur.getD t 0#32)
    (hpermP : ((List.range (o1.toNat - lo)).map (fun t => (bP.getD (lo + t) 0#32).toNat) ++
        (List.range (mid - p1.toNat)).map (fun t => (aArr.getD (p1.toNat + t) 0#32).toNat) ++
        (List.range (hi - qNat)).map (fun t => (aArr.getD (qNat + t) 0#32).toNat)).Perm
        ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat)))
    (ho1_p1 : (o1 + 1#32).toNat = o1.toNat + 1) (hp1_p1 : (p1 + 1#32).toNat = p1.toNat + 1)
    (hm' : (array (t := i32) aPtr aArr ⋆
      array (t := i32) bPtr (bP.set o1.toNat (aArr[p1.toNat]'hp1_a)) ⋆ Rmerge) m') :
    MergePInv aPtr bPtr aArr bArr bCur lo mid hi qNat Rmerge
      (mid - (p1 + 1#32).toNat) (p1 + 1#32, o1 + 1#32, ⟨⟩) m' := by
  refine ⟨rfl, ?_⟩
  rw [ho1_p1, hp1_p1]
  exact MergeChunkInv.step_p hbP_len hlo_p1 hp1_lt hmid_q hq_hi ho1_eq ho1_lt hp1_a
    hkeepP hpermP hm'

private theorem sort_combine_jq_next {aPtr bPtr : BitVec 64}
    {aArr bArr bCur bQ : List (BitVec 32)}
    {lo mid hi : Nat} {q1 o2 : BitVec 32} {Rmerge : Mem 64 → Prop} {m' : Mem 64}
    (hbQ_len : bQ.length = bArr.length) (hlo_mid : lo ≤ mid)
    (hmid_q1 : mid ≤ q1.toNat) (hq1_lt : q1.toNat < hi)
    (ho2_eq : o2.toNat = lo + (mid - lo) + (q1.toNat - mid)) (ho2_lt : o2.toNat < bQ.length)
    (hq1_a : q1.toNat < aArr.length) (hkeepQ : ∀ t < lo, bQ.getD t 0#32 = bCur.getD t 0#32)
    (hpermQ : ((List.range (o2.toNat - lo)).map (fun t => (bQ.getD (lo + t) 0#32).toNat) ++
        (List.range (mid - mid)).map (fun t => (aArr.getD (mid + t) 0#32).toNat) ++
        (List.range (hi - q1.toNat)).map (fun t => (aArr.getD (q1.toNat + t) 0#32).toNat)).Perm
        ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat)))
    (ho2_p1 : (o2 + 1#32).toNat = o2.toNat + 1) (hq1_p1 : (q1 + 1#32).toNat = q1.toNat + 1)
    (hm' : (array (t := i32) aPtr aArr ⋆
      array (t := i32) bPtr (bQ.set o2.toNat (aArr[q1.toNat]'hq1_a)) ⋆ Rmerge) m') :
    MergeQInv aPtr bPtr aArr bArr bCur lo mid hi Rmerge
      (hi - (q1 + 1#32).toNat) (q1 + 1#32, o2 + 1#32, ⟨⟩) m' := by
  refine ⟨rfl, ?_⟩
  rw [ho2_p1, hq1_p1]
  exact MergeChunkInv.step_q hbQ_len hlo_mid (le_refl _) hmid_q1 hq1_lt ho2_eq ho2_lt hq1_a
    hkeepQ hpermQ hm'

private theorem sort_combine_combine_emit {nOut qn : Nat}
    {srcPool qm : List (BitVec 32)} {ql qh qlC qhC : List (BitVec 64)}
    {aArr aC : List (BitVec 32)} {qlPtr qhPtr ixPtr : BitVec 64} {Rcmb : Mem 64 → Prop}
    {m' : Mem 64} {k i j : BitVec 32} {l h : BitVec 64} {h0 : BitVec 32}
    (hqlC_len : qlC.length = ql.length) (hqhC_len : qhC.length = qh.length)
    (haC_len : aC.length = aArr.length) (hk_i : k.toNat ≤ i.toNat) (hi_lt : i.toNat < qn)
    (hj_lo : i.toNat + 1 ≤ j.toNat) (hj_qn : j.toNat ≤ qn)
    (hh0_eq : h0 = aArr.getD i.toNat 0#32) (hpermA : PermN aArr qn)
    (hqn_ql : qn ≤ ql.length) (hqn_qh : qn ≤ qh.length) (hk_aC : k.toNat < aC.length)
    (hsrcA : ∀ p < k.toNat, ∃ idx < i.toNat, aC.getD p 0#32 = aArr.getD idx 0#32)
    (hrestA : ∀ t, i.toNat ≤ t → t < qn → aC.getD t 0#32 = aArr.getD t 0#32)
    (hndA : ((List.range k.toNat).map (fun p => (aC.getD p 0#32).toNat)).Nodup)
    (hltA : ∀ p < k.toNat, (aC.getD p 0#32).toNat < qn)
    (hqlUnmod : ∀ idx, (∀ p < k.toNat, (aC.getD p 0#32).toNat ≠ idx) →
      qlC.getD idx 0#64 = ql.getD idx 0#64 ∧ qhC.getD idx 0#64 = qh.getD idx 0#64)
    (hjSum : ∀ σ : Nat → Bool,
      (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
        polyEvalIdxOf nOut σ srcPool qm ql qh aArr j.toNat (qn - j.toNat) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i.toNat (qn - i.toNat))
    (hevalC : ∀ σ : Nat → Bool,
      polyEvalIdxOf nOut σ srcPool qm qlC qhC aC 0 k.toNat +
        polyEvalIdxOf nOut σ srcPool qm ql qh aArr i.toNat (qn - i.toNat) =
      polyEval nOut σ srcPool qm ql qh qn)
    (hkp1 : (k + 1#32).toNat = k.toNat + 1)
    (hm' : (array64 qlPtr (qlC.set h0.toNat l) ⋆ array64 qhPtr (qhC.set h0.toNat h) ⋆
      array (t := i32) ixPtr (aC.set k.toNat h0) ⋆ Rcmb) m') :
    CombineLoopInv nOut qn srcPool qm ql qh aArr qlPtr qhPtr ixPtr Rcmb
      (qn - j.toNat) (j, k + 1#32, ⟨⟩) m' := by
  refine ⟨rfl, ?_⟩; rw [hkp1]
  exact CombineInv.step_emit hqlC_len hqhC_len haC_len hk_i hi_lt hj_lo hj_qn hh0_eq hpermA
    hqn_ql hqn_qh hk_aC hsrcA hrestA hndA hltA hqlUnmod hjSum hevalC hm'

private theorem sort_combine_jj_step {nOut qn : Nat}
    {srcPool qm : List (BitVec 32)} {ql qh qlC qhC : List (BitVec 64)}
    {aArr aC : List (BitVec 32)} {h0 : BitVec 32} {mC : Mem 64}
    {i j : BitVec 32} {l h nl nh : BitVec 64} {hj_aC : j.toNat < aC.length}
    (hj_lt : j.toNat < qn) (hj_lo : i.toNat + 1 ≤ j.toNat)
    (haj_ql : (aC[j.toNat]'hj_aC).toNat < qlC.length)
    (haj_qh : (aC[j.toNat]'hj_aC).toNat < qhC.length)
    (haj_eq : aC[j.toNat]'hj_aC = aArr.getD j.toNat 0#32)
    (haj_unmod : qlC.getD (aArr.getD j.toNat 0#32).toNat 0#64 =
        ql.getD (aArr.getD j.toNat 0#32).toNat 0#64 ∧
      qhC.getD (aArr.getD j.toNat 0#32).toNat 0#64 =
        qh.getD (aArr.getD j.toNat 0#32).toNat 0#64)
    (hsym : symListAt srcPool (qm.getD (aArr.getD j.toNat 0#32).toNat 0#32).toNat =
      symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
    (hcadd : coeff128 nOut nl nh =
      coeff128 nOut l h + coeff128 nOut (qlC[aC[j.toNat].toNat]'haj_ql)
        (qhC[aC[j.toNat].toNat]'haj_qh))
    (hjp1 : (j + 1#32).toNat = j.toNat + 1)
    (hjSum : ∀ σ : Nat → Bool,
      (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
        polyEvalIdxOf nOut σ srcPool qm ql qh aArr j.toNat (qn - j.toNat) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i.toNat (qn - i.toNat)) :
    CombineJInv nOut qn i.toNat srcPool qm ql qh aArr h0 mC
      (qn - (j + 1#32).toNat) (nl, nh, j + 1#32, ⟨⟩) mC := by
  have hcadd' := combine_cadd_coeff haj_ql haj_qh haj_eq haj_unmod hcadd
  refine ⟨rfl, by omega, by omega, rfl, fun σ => ?_⟩
  rw [hjp1]; exact combine_cadd_step hj_lt hsym hcadd' (hjSum σ)

private theorem sort_combine_combine_skip {nOut qn : Nat}
    {srcPool qm : List (BitVec 32)} {ql qh qlC qhC : List (BitVec 64)}
    {aArr aC : List (BitVec 32)} {qlPtr qhPtr ixPtr : BitVec 64} {Rcmb : Mem 64 → Prop}
    {mC : Mem 64} {k i j : BitVec 32} {l h : BitVec 64} {h0 : BitVec 32}
    (hqlC_len : qlC.length = ql.length) (hqhC_len : qhC.length = qh.length)
    (haC_len : aC.length = aArr.length) (hk_i : k.toNat ≤ i.toNat)
    (hj_lo : i.toNat + 1 ≤ j.toNat) (hj_qn : j.toNat ≤ qn)
    (hl0 : l = 0#64) (hh0' : h = 0#64)
    (hsrcA : ∀ p < k.toNat, ∃ idx < i.toNat, aC.getD p 0#32 = aArr.getD idx 0#32)
    (hrestA : ∀ t, i.toNat ≤ t → t < qn → aC.getD t 0#32 = aArr.getD t 0#32)
    (hndA : ((List.range k.toNat).map (fun p => (aC.getD p 0#32).toNat)).Nodup)
    (hltA : ∀ p < k.toNat, (aC.getD p 0#32).toNat < qn)
    (hqlUnmod : ∀ idx, (∀ p < k.toNat, (aC.getD p 0#32).toNat ≠ idx) →
      qlC.getD idx 0#64 = ql.getD idx 0#64 ∧ qhC.getD idx 0#64 = qh.getD idx 0#64)
    (hjSum : ∀ σ : Nat → Bool,
      (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
        polyEvalIdxOf nOut σ srcPool qm ql qh aArr j.toNat (qn - j.toNat) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i.toNat (qn - i.toNat))
    (hevalC : ∀ σ : Nat → Bool,
      polyEvalIdxOf nOut σ srcPool qm qlC qhC aC 0 k.toNat +
        polyEvalIdxOf nOut σ srcPool qm ql qh aArr i.toNat (qn - i.toNat) =
      polyEval nOut σ srcPool qm ql qh qn)
    (hmC : (array64 qlPtr qlC ⋆ array64 qhPtr qhC ⋆ array (t := i32) ixPtr aC ⋆ Rcmb) mC) :
    CombineLoopInv nOut qn srcPool qm ql qh aArr qlPtr qhPtr ixPtr Rcmb
      (qn - j.toNat) (j, k, ⟨⟩) mC :=
  ⟨rfl, CombineInv.step_skip hqlC_len hqhC_len haC_len hk_i hj_lo hj_qn hl0 hh0' hsrcA hrestA
    hndA hltA hqlUnmod hjSum hevalC hmC⟩

private def sortCombineMergeExpr (cx : Val i64) (n : Val i32)
    (ix ix2 pool qm : Val i64) : Expr Val Cont [i32] :=
  match ar_sort_combine_body Val Cont (cx, ()) with
  | @Expr.let_ _ _ _ [.bits 64] _ k1 => match k1 (cx + 684#64, ()) with
    | @Expr.load _ _ _ (.bits 32) _ k2 => match k2 n with
      | @Expr.let_ _ _ _ [.bits 64] _ k3 => match k3 (cx + 472#64, ()) with
        | @Expr.load _ _ _ (.bits 64) _ k4 => match k4 ix with
          | @Expr.let_ _ _ _ [.bits 64] _ k5 => match k5 (cx + 480#64, ()) with
            | @Expr.load _ _ _ (.bits 64) _ k6 => match k6 ix2 with
              | @Expr.let_ _ _ _ [.bits 64] _ k7 => match k7 (cx + 408#64, ()) with
                | @Expr.let_ _ _ _ [.bits 64] _ k8 => match k8 (cx + 680#64, ()) with
                  | @Expr.load _ _ _ (.bits 32) _ k9 => match k9 0#32 with
                    | @Expr.let_ _ _ _ [.bits 64] _ k10 => match k10 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ k11 => match k11 (0#64, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ k12 => match k12 (cx + 408#64, ()) with
                          | @Expr.load _ _ _ (.bits 64) _ k13 => match k13 pool with
                            | @Expr.let_ _ _ _ [.bits 64] _ k14 => match k14 (cx + 440#64, ()) with
                              | @Expr.load _ _ _ (.bits 64) _ k15 => match k15 qm with
                                | @Expr.group _ _ _ [[.bits 32]] bs1 _ =>
                                  match bs1 (fun _ _ => False, ()) with
                                  | .cons b1 _ => match b1 (0#32, ()) with
                                    | @Expr.let_ _ _ _ [.bool] _ kb1 => match kb1 (false, ()) with
                                      | .jnz _ _ eIns => match eIns with
                                        | @Expr.group _ _ _ [[.bits 32]] bs2 _ =>
                                          match bs2 (fun _ _ => False, ()) with
                                          | .cons b2 _ => match b2 (0#32, ()) with
                                            | @Expr.let_ _ _ _ [.bool] _ kb2 =>
                                              match kb2 (false, ()) with
                                              | .jnz _ _ eMerge => eMerge
                                              | _ => .ret (Arg.imm 0, ())
                                            | _ => .ret (Arg.imm 0, ())
                                          | _ => .ret (Arg.imm 0, ())
                                        | _ => .ret (Arg.imm 0, ())
                                      | _ => .ret (Arg.imm 0, ())
                                    | _ => .ret (Arg.imm 0, ())
                                  | _ => .ret (Arg.imm 0, ())
                                | _ => .ret (Arg.imm 0, ())
                              | _ => .ret (Arg.imm 0, ())
                            | _ => .ret (Arg.imm 0, ())
                          | _ => .ret (Arg.imm 0, ())
                        | _ => .ret (Arg.imm 0, ())
                      | _ => .ret (Arg.imm 0, ())
                    | _ => .ret (Arg.imm 0, ())
                  | _ => .ret (Arg.imm 0, ())
                | _ => .ret (Arg.imm 0, ())
              | _ => .ret (Arg.imm 0, ())
            | _ => .ret (Arg.imm 0, ())
          | _ => .ret (Arg.imm 0, ())
        | _ => .ret (Arg.imm 0, ())
      | _ => .ret (Arg.imm 0, ())
    | _ => .ret (Arg.imm 0, ())
  | _ => .ret (Arg.imm 0, ())

private def sortCombineCombineExpr (cx : Val i64) (n : Val i32)
    (ix ix2 pool qm aPtr bPtr : Val i64) : Expr Val Cont [i32] :=
  match sortCombineMergeExpr cx n ix ix2 pool qm with
  | @Expr.group _ _ _ [[.bits 64, .bits 64, .bits 64]] bs3 _ =>
    match bs3 (fun _ _ => False, ()) with
    | .cons b3 _ => match b3 (aPtr, bPtr, 16#64, ()) with
      | @Expr.let_ _ _ _ [.bits 64] _ kb3a => match kb3a (BitVec.setWidth 64 n, ()) with
        | @Expr.let_ _ _ _ [.bool] _ kb3b => match kb3b (false, ()) with
          | .jnz _ _ eCombine => eCombine
          | _ => .ret (Arg.imm 0, ())
        | _ => .ret (Arg.imm 0, ())
      | _ => .ret (Arg.imm 0, ())
    | _ => .ret (Arg.imm 0, ())
  | _ => .ret (Arg.imm 0, ())

private def sortCombineJExitExpr (cx : Val i64) (n : Val i32)
    (ix ix2 pool qm aPtr bPtr qlPtr qhPtr : Val i64)
    (i k h0 j : Val i32) (l h : Val i64) (JC : Cont [i32, i32]) : Expr Val Cont [i32] :=
  match sortCombineCombineExpr cx n ix ix2 pool qm aPtr bPtr with
  | @Expr.let_ _ _ _ [.bits 64] _ k1 => match k1 (cx + 472#64, ()) with
    | .store _ _ k2 => match k2 with
      | @Expr.let_ _ _ _ [.bits 64] _ k3 => match k3 (cx + 480#64, ()) with
        | .store _ _ k4 => match k4 with
          | @Expr.group _ _ _ [[.bits 32, .bits 32]] bs _ =>
            match bs (JC, ()) with
            | .cons bc _ => match bc (i, k, ()) with
              | @Expr.let_ _ _ _ [.bool] _ kc => match kc (false, ()) with
                | .jnz _ eT _ => match eT with
                  | @Expr.let_ _ _ _ [.bits 64] _ e1 => match e1 (0#64, ()) with
                    | @Expr.let_ _ _ _ [.bits 64] _ e2 => match e2 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ e3 => match e3 (0#64, ()) with
                        | @Expr.load _ _ _ (.bits 32) _ e4 => match e4 h0 with
                          | @Expr.let_ _ _ _ [.bits 64] _ e5 => match e5 (cx + 456#64, ()) with
                            | @Expr.load _ _ _ (.bits 64) _ e6 => match e6 qlPtr with
                              | @Expr.let_ _ _ _ [.bits 64] _ e7 => match e7 (0#64, ()) with
                                | @Expr.let_ _ _ _ [.bits 64] _ e8 => match e8 (0#64, ()) with
                                  | @Expr.let_ _ _ _ [.bits 64] _ e9 => match e9 (0#64, ()) with
                                    | @Expr.load _ _ _ (.bits 64) _ e10 => match e10 l with
                                      | @Expr.let_ _ _ _ [.bits 64] _ e11 =>
                                        match e11 (cx + 464#64, ()) with
                                        | @Expr.load _ _ _ (.bits 64) _ e12 =>
                                          match e12 qhPtr with
                                          | @Expr.let_ _ _ _ [.bits 64] _ e13 =>
                                            match e13 (0#64, ()) with
                                            | @Expr.let_ _ _ _ [.bits 64] _ e14 =>
                                              match e14 (0#64, ()) with
                                              | @Expr.let_ _ _ _ [.bits 64] _ e15 =>
                                                match e15 (0#64, ()) with
                                                | @Expr.load _ _ _ (.bits 64) _ e16 =>
                                                  match e16 h with
                                                  | @Expr.let_ _ _ _ [.bits 32] _ e17 =>
                                                    match e17 (0#32, ()) with
                                                    | @Expr.group _ _ _
                                                        [[.bits 64, .bits 64, .bits 32]] bsJ _ =>
                                                      match bsJ (fun _ _ => False, ()) with
                                                      | .cons bJ _ => match bJ (l, h, j, ()) with
                                                        | @Expr.group _ _ _ [[]] bsExit _ =>
                                                          match bsExit (fun _ _ => False, ()) with
                                                          | .cons bExit _ => bExit ()
                                                          | _ => .ret (Arg.imm 0, ())
                                                        | _ => .ret (Arg.imm 0, ())
                                                      | _ => .ret (Arg.imm 0, ())
                                                    | _ => .ret (Arg.imm 0, ())
                                                  | _ => .ret (Arg.imm 0, ())
                                                | _ => .ret (Arg.imm 0, ())
                                              | _ => .ret (Arg.imm 0, ())
                                            | _ => .ret (Arg.imm 0, ())
                                          | _ => .ret (Arg.imm 0, ())
                                        | _ => .ret (Arg.imm 0, ())
                                      | _ => .ret (Arg.imm 0, ())
                                    | _ => .ret (Arg.imm 0, ())
                                  | _ => .ret (Arg.imm 0, ())
                                | _ => .ret (Arg.imm 0, ())
                              | _ => .ret (Arg.imm 0, ())
                            | _ => .ret (Arg.imm 0, ())
                          | _ => .ret (Arg.imm 0, ())
                        | _ => .ret (Arg.imm 0, ())
                      | _ => .ret (Arg.imm 0, ())
                    | _ => .ret (Arg.imm 0, ())
                  | _ => .ret (Arg.imm 0, ())
                | _ => .ret (Arg.imm 0, ())
              | _ => .ret (Arg.imm 0, ())
            | _ => .ret (Arg.imm 0, ())
          | _ => .ret (Arg.imm 0, ())
        | _ => .ret (Arg.imm 0, ())
      | _ => .ret (Arg.imm 0, ())
    | _ => .ret (Arg.imm 0, ())
  | _ => .ret (Arg.imm 0, ())

private theorem sort_combine_j_exit (Γ : T.Env)
    {cx : Val i64} {Q : Post [i32]} {X : XPost} {s : ArCtxState}
    {srcPool qm : List (BitVec 32)} {ql qh qlC qhC : List (BitVec 64)}
    {aArr aC : List (BitVec 32)} {poolPtr aPtr bPtr qlPtr qhPtr : BitVec 64}
    {Rcmb Rcmb0 : Mem 64 → Prop} {JC : Cont [i32, i32]} {irem : Nat}
    {i k h0 j : BitVec 32} {l h : BitVec 64} {mC : Mem 64}
    (hrecC : ∀ (n' : Nat) (ys : Tup Val [i32, i32]) (m' : Mem 64), n' < irem →
      CombineLoopInv s.modW s.qn.toNat srcPool qm ql qh aArr
        s.ql s.qh { s with ix := aPtr, ix2 := bPtr }.ix Rcmb n' ys m' → JC ys m')
    (hirem : irem = s.qn.toNat - i.toNat) (hqlC_len : qlC.length = ql.length)
    (hqhC_len : qhC.length = qh.length) (haC_len : aC.length = aArr.length)
    (hk_i : k.toNat ≤ i.toNat) (hi_lt : i.toNat < s.qn.toNat)
    (hj_lo : i.toNat + 1 ≤ j.toNat) (hj_qn : j.toNat ≤ s.qn.toNat)
    (hh0_eq : h0 = aArr.getD i.toNat 0#32) (hpermA : PermN aArr s.qn.toNat)
    (hql_len : s.qn.toNat ≤ ql.length) (hqh_len : s.qn.toNat ≤ qh.length)
    (hk_aC : k.toNat < aC.length) (hqn32 : s.qn.toNat + 1 < 2 ^ 32)
    (hsrcA : ∀ p < k.toNat, ∃ idx < i.toNat, aC.getD p 0#32 = aArr.getD idx 0#32)
    (hrestA : ∀ t, i.toNat ≤ t → t < s.qn.toNat → aC.getD t 0#32 = aArr.getD t 0#32)
    (hndA : ((List.range k.toNat).map (fun p => (aC.getD p 0#32).toNat)).Nodup)
    (hltA : ∀ p < k.toNat, (aC.getD p 0#32).toNat < s.qn.toNat)
    (hqlUnmod : ∀ idx, (∀ p < k.toNat, (aC.getD p 0#32).toNat ≠ idx) →
      qlC.getD idx 0#64 = ql.getD idx 0#64 ∧ qhC.getD idx 0#64 = qh.getD idx 0#64)
    (hjSum : ∀ σ : Nat → Bool,
      (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 s.modW l h else 0#s.modW) +
        polyEvalIdxOf s.modW σ srcPool qm ql qh aArr j.toNat (s.qn.toNat - j.toNat) =
      polyEvalIdxOf s.modW σ srcPool qm ql qh aArr i.toNat (s.qn.toNat - i.toNat))
    (hevalC : ∀ σ : Nat → Bool,
      polyEvalIdxOf s.modW σ srcPool qm qlC qhC aC 0 k.toNat +
        polyEvalIdxOf s.modW σ srcPool qm ql qh aArr i.toNat (s.qn.toNat - i.toNat) =
      polyEval s.modW σ srcPool qm ql qh s.qn.toNat)
    (hql_eq : qlPtr = s.ql) (hqh_eq : qhPtr = s.qh)
    (hRcmb : Rcmb = arCtxMem cx { s with ix := aPtr, ix2 := bPtr } ⋆ Rcmb0)
    (hh0_ql : h0.toNat < qlC.length) (hh0_qh : h0.toNat < qhC.length)
    (hmC : (array64 s.ql qlC ⋆ array64 s.qh qhC ⋆
      array (t := i32) { s with ix := aPtr, ix2 := bPtr }.ix aC ⋆
      arCtxMem cx { s with ix := aPtr, ix2 := bPtr } ⋆ Rcmb0) mC) :
    wp Γ Q X (sortCombineJExitExpr cx s.qn s.ix s.ix2 poolPtr s.qm aPtr bPtr
      qlPtr qhPtr i k h0 j l h JC) mC := by
  subst qlPtr qhPtr
  dsimp only [sortCombineJExitExpr, sortCombineCombineExpr, sortCombineMergeExpr]
  c0_hfast_nogrp
  refine wp_join_group (fun (v : Tup Val [.bits 32]) mK =>
      CombineLoopInv s.modW s.qn.toNat srcPool qm ql qh aArr s.ql s.qh
        { s with ix := aPtr, ix2 := bPtr }.ix Rcmb (s.qn.toNat - j.toNat) (j, v.1, ⟨⟩) mK)
    ?_ ?_
  · rintro JK ⟨k', ⟨⟩⟩ mK hinvK
    c0_hfast
    exact hrecC (s.qn.toNat - j.toNat) (j, k', ⟨⟩) mK (by omega) hinvK
  · intro JK hJK
    c0_hfast_nogrp
    refine wp_join_group (fun (_ : Tup Val []) mE => mE = mC) ?_ ?_
    · rintro JE ⟨⟩ mE rfl
      have hkp1 : (k + 1#32).toNat = k.toNat + 1 := bv32_succ_toNat (by omega)
      c0_hfast_nogrp
      exact hJK (k + 1#32, ⟨⟩) m (sort_combine_combine_emit hqlC_len hqhC_len haC_len hk_i hi_lt
        hj_lo hj_qn hh0_eq hpermA hql_len hqh_len hk_aC hsrcA hrestA hndA hltA hqlUnmod hjSum
        hevalC hkp1 (by
          simp only [bv64_zext32_toNat] at hm
          rw [hRcmb]; exact sep_cast hm (by ac_rfl)))
    · intro JE hJE
      c0_hsplit
      · exact hJE ⟨⟩ mC rfl
      · c0_hsplit
        · exact hJE ⟨⟩ mC rfl
        · have hl0 : l = 0#64 := by c0_bv_omega
          have hh0' : h = 0#64 := by c0_bv_omega
          c0_hfast_nogrp
          exact hJK (k, ⟨⟩) mC (sort_combine_combine_skip hqlC_len hqhC_len haC_len hk_i hj_lo hj_qn
            hl0 hh0' hsrcA hrestA hndA hltA hqlUnmod hjSum hevalC
            (by rw [hRcmb]; exact sep_cast hmC (by ac_rfl)))

private theorem sort_combine_combine_phase (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx : Val i64} {Q : Post [i32]} {X : XPost} {s : ArCtxState}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {R restTQ Rbase : Mem 64 → Prop}
    {poolPtr aPtr bPtr : BitVec 64} {aArr bArr : List (BitVec 32)} {mW : Mem 64}
    (_hpc : s.pc.toNat < 2) (hqn_le : s.qn.toNat ≤ s.qcap.toNat)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32)
    (hqm_len : s.qcap.toNat ≤ qm.length) (hql_len : s.qcap.toNat ≤ ql.length)
    (hqh_len : s.qcap.toNat ≤ qh.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (hix2_len : s.qcap.toNat ≤ ix2.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hQmOk : ∀ i < s.qn.toNat,
      MonoSliceOk (if s.pc.toNat = 0 then pool0 else pool1) (qm.getD i 0#32).toNat
        (if s.pc.toNat = 0 then pool0 else pool1).length ∧
      ((if s.pc.toNat = 0 then pool0 else pool1).getD
          (qm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hpool_eq : poolPtr = s.pool.getD s.pc.toNat 0#64)
    (hRbase : Rbase = restTQ ⋆ R)
    (hfoc : ∀ (s' : ArCtxState) (ql' qh' : List (BitVec 64)) (ix' ix2' : List (BitVec 32)),
      s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
      s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh → s'.bx = s.bx →
      s'.vq_off = s.vq_off → s'.vq = s.vq → s'.vq_skip = s.vq_skip →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧ ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
        (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧ ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          qMem s' qm qs ql' qh' ix' ix2' bx vqOff vq vqSkip =
        array (t := i32) (s.pool.getD s.pc.toNat 0#64)
          (if s.pc.toNat = 0 then pool0 else pool1) ⋆
        array (t := i32) s.qm qm ⋆ array64 s.ql ql' ⋆ array64 s.qh qh' ⋆
        array (t := i32) s'.ix ix' ⋆ array (t := i32) s'.ix2 ix2' ⋆ restTQ)
    (hptrs : (aPtr = s.ix ∧ bPtr = s.ix2 ∧ aArr.length = ix.length ∧ bArr.length = ix2.length) ∨
      (aPtr = s.ix2 ∧ bPtr = s.ix ∧ aArr.length = ix2.length ∧ bArr.length = ix.length))
    (hpermA : PermN aArr s.qn.toNat)
    (hmW : (arCtxMem cx s ⋆
      array (t := i32) (s.pool.getD s.pc.toNat 0#64) (if s.pc.toNat = 0 then pool0 else pool1) ⋆
      array (t := i32) s.qm qm ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
      array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bArr ⋆ Rbase) mW)
    (hQ : ∀ (k : BitVec 32) (s' : ArCtxState) (ql' qh' : List (BitVec 64))
        (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      k.toNat ≤ s.qn.toNat → ql'.length = ql.length → qh'.length = qh.length →
      s.qcap.toNat ≤ ix'.length → s.qcap.toNat ≤ ix2'.length →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
        ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
        ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      s' = { s with ix := s'.ix, ix2 := s'.ix2 } →
      (∀ p < k.toNat, (ix'.getD p 0#32).toNat < s.qn.toNat) →
      ((List.range k.toNat).map (fun p => (ix'.getD p 0#32).toNat)).Nodup →
      (∀ σ : Nat → Bool,
        polyEvalIdxOf s.modW σ (if s.pc.toNat = 0 then pool0 else pool1)
          qm ql' qh' ix' 0 k.toNat =
          polyEval s.modW σ (if s.pc.toNat = 0 then pool0 else pool1)
            qm ql qh s.qn.toNat) →
      (arCtxMem cx s' ⋆ tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s' qm qs ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆ R) m' → Q (k, ⟨⟩) m') :
    wp Γ Q X (sortCombineCombineExpr cx s.qn s.ix s.ix2 poolPtr s.qm aPtr bPtr) mW := by
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  have hl_s : ArCtxLengthsOk s :=
    arCtxMem_lengths4 (sep_cast hmW (by ac_rfl) :
      (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) s.qm qm ⋆
        (array64 s.ql ql ⋆ array64 s.qh qh ⋆ array (t := i32) aPtr aArr ⋆
          array (t := i32) bPtr bArr ⋆ Rbase)) mW)
  have hpool_pc : poolPtr = s.pool.getD s.pc.toNat 0#64 := hpool_eq
  have ha_qcap : s.qcap.toNat ≤ aArr.length ∧ s.qcap.toNat ≤ bArr.length := by
    rcases hptrs with ⟨_, _, ha, hb⟩ | ⟨_, _, ha, hb⟩ <;> omega
  dsimp only [sortCombineCombineExpr, sortCombineMergeExpr]
  c0_hfast_nogrp
  let sMid : ArCtxState := { s with ix := aPtr, ix2 := bPtr }
  have hmMid : (arCtxMem cx sMid ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) s.qm qm ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
      array (t := i32) sMid.ix aArr ⋆ array (t := i32) sMid.ix2 bArr ⋆ Rbase) _ :=
    sep_cast hm (by dsimp only [sMid]; ac_rfl)
  try clear hmW; try clear hm; try clear hm
  let Rcmb0 := array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
    array (t := i32) s.qm qm ⋆ array (t := i32) sMid.ix2 bArr ⋆ Rbase
  let Rcmb := arCtxMem cx sMid ⋆ Rcmb0
  have hRcmb : Rcmb = arCtxMem cx sMid ⋆ Rcmb0 := rfl
  refine wp_loop_group (CombineLoopInv s.modW s.qn.toNat srcPool qm ql qh
      aArr s.ql s.qh sMid.ix Rcmb) ?_ ?_
  · intro JC irem ⟨i, k, ⟨⟩⟩ mC hrecC ⟨hirem, qlC, qhC, aC, hqlC_len, hqhC_len,
        haC_len, hk_i, hi_qn, hsrcA, hrestA, hndA, hltA, hqlUnmod, hevalC, hmC⟩
    clear hmMid; c0_hsplit
    · have hi_lt : i.toNat < s.qn.toNat := hc
      clear hc
      have hi_aC : i.toNat < aC.length := by omega
      have hip1 : (i + 1#32).toNat = i.toNat + 1 := bv32_succ_toNat (by have := s.qn.isLt; omega)
      let h0 := aC[i.toNat]'hi_aC
      have hh0_eq : h0 = aArr.getD i.toNat 0#32 := by
        dsimp only [h0]
        rw [← getD_eq_getElem aC 0#32 hi_aC]
        exact hrestA i.toNat (le_refl _) hi_lt
      have hh0_lt : h0.toNat < s.qn.toNat := by rw [hh0_eq]; exact hpermA.mem_lt hi_lt
      have hh0_ql : h0.toNat < qlC.length := by omega
      have hh0_qh : h0.toNat < qhC.length := by omega
      have hql_ac : (aC[(BitVec.setWidth 64 i).toNat]'(by simp; omega)).toNat < qlC.length := by
        simpa [bv64_zext32_toNat] using hh0_ql
      have hqh_ac : (aC[(BitVec.setWidth 64 i).toNat]'(by simp; omega)).toNat < qhC.length := by
        simpa [bv64_zext32_toNat] using hh0_qh
      have hh0_unmod : qlC.getD h0.toNat 0#64 = ql.getD h0.toNat 0#64 ∧
          qhC.getD h0.toNat 0#64 = qh.getD h0.toNat 0#64 := by
        rw [hh0_eq]; exact combine_idx_unmod hpermA hi_lt hsrcA (le_refl _) hqlUnmod
      have hmC0 : (array64 s.ql qlC ⋆ array64 s.qh qhC ⋆ array (t := i32) sMid.ix aC ⋆
          arCtxMem cx sMid ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
          array (t := i32) s.qm qm ⋆ array (t := i32) sMid.ix2 bArr ⋆ Rbase) mC := by
        dsimp only [Rcmb, Rcmb0] at hmC; exact sep_cast hmC (by ac_rfl)
      have hmC0_exit : (array64 s.ql qlC ⋆ array64 s.qh qhC ⋆ array (t := i32) sMid.ix aC ⋆
          arCtxMem cx sMid ⋆ Rcmb0) mC := by
        dsimp only [Rcmb] at hmC; exact sep_cast hmC (by ac_rfl)
      c0_hfast_nogrp
      refine wp_loop_group
        (CombineJInv s.modW s.qn.toNat i.toNat srcPool qm ql qh aArr h0 mC) ?_ ?_
      · intro JJ jrem ⟨l, h, j, ⟨⟩⟩ mJ hrecJ ⟨hmJ, hj_lo, hj_qn, hjrem, hjSum⟩
        subst mJ
        refine wp_join_group (fun (_ : Tup Val []) mE => mE = mC) ?_ ?_
        · rintro JE ⟨⟩ mE hmE
          rw [hmE] at *
          change wp Γ Q X (sortCombineJExitExpr cx s.qn s.ix s.ix2 poolPtr s.qm aPtr bPtr
            s.ql s.qh i k h0 j l h JC) mC
          exact sort_combine_j_exit Γ hrecC hirem hqlC_len hqhC_len haC_len hk_i hi_lt hj_lo
            hj_qn hh0_eq hpermA (by omega) (by omega) (by omega) (by omega) hsrcA hrestA hndA
            hltA hqlUnmod hjSum hevalC rfl rfl hRcmb hh0_ql hh0_qh hmC0_exit
        · intro JE hJE
          c0_hsplit
          · have hj_lt : j.toNat < s.qn.toNat := hc
            clear hc
            have hj_aC : j.toNat < aC.length := by omega
            have haj_eq : aC[j.toNat]'hj_aC = aArr.getD j.toNat 0#32 := by
              rw [← getD_eq_getElem aC 0#32 hj_aC]; exact hrestA j.toNat (by omega) hj_lt
            have haj_lt : (aC[j.toNat]'hj_aC).toNat < s.qn.toNat := by
              rw [haj_eq]; exact hpermA.mem_lt hj_lt
            have haj_qm' : (aC[j.toNat]'hj_aC).toNat < qm.length := by omega
            have hh0_qm' : h0.toNat < qm.length := by omega
            let Rmc := arCtxMem cx sMid ⋆ array (t := i32) s.qm qm ⋆
              array64 s.ql qlC ⋆ array64 s.qh qhC ⋆
              array (t := i32) sMid.ix aC ⋆ array (t := i32) sMid.ix2 bArr ⋆ Rbase
            c0_hstraight; refine wp_call_of_spec _ _ (hMcmp _ _ _ _
              ⟨s.pool.getD s.pc.toNat 0#64, srcPool,
                (qm.getD (aC[j.toNat]'hj_aC).toNat 0#32).toNat, (qm.getD h0.toNat 0#32).toNat, Rmc,
                (by simp only [Arg.val, bv64_zext32_toNat]
                    exact qm_pool_ptr_eq _ _ qm haj_qm' hpool_pc),
                (by simp only [Arg.val, bv64_zext32_toNat]
                    exact qm_pool_ptr_eq _ _ qm hh0_qm' hpool_pc),
                (hQmOk _ haj_lt).1, (hQmOk _ hh0_lt).1, (hQmOk _ haj_lt).2,
                sep_cast hmC0 (by dsimp only [Rmc]; ac_rfl), fun cmp hcmp => ?_⟩)
            · c0_hsplit
              · have hsym : symListAt srcPool (qm.getD (aArr.getD j.toNat 0#32).toNat 0#32).toNat =
                    symListAt srcPool (qm.getD h0.toNat 0#32).toNat := by
                  simpa [haj_eq] using hcmp hc
                clear hc
                have haj_ql : (aC[j.toNat]'hj_aC).toNat < qlC.length := by omega
                have haj_qh : (aC[j.toNat]'hj_aC).toNat < qhC.length := by omega
                have haj_unmod := combine_idx_unmod hpermA hj_lt hsrcA (by omega) hqlUnmod
                let Rcadd := array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
                  array (t := i32) s.qm qm ⋆ array64 s.ql qlC ⋆ array64 s.qh qhC ⋆
                  array (t := i32) sMid.ix aC ⋆ array (t := i32) sMid.ix2 bArr ⋆ Rbase
                c0_hfast; refine wp_call_of_spec _ _ (hCadd _ _ _ _
                  ⟨sMid, Rcadd, hMasks, sep_cast hmC0 (by dsimp only [Rcadd]; ac_rfl),
                    fun nl nh hcadd => ?_⟩)
                have hjp1 : (j + 1#32).toNat = j.toNat + 1 :=
                  bv32_succ_toNat (by have := s.qn.isLt; omega)
                c0_hfast; exact hrecJ (s.qn.toNat - (j + 1#32).toNat) (nl, nh, j + 1#32, ⟨⟩) mC
                  (by omega) (sort_combine_jj_step hj_lt (by omega) haj_ql haj_qh haj_eq
                    haj_unmod hsym hcadd hjp1 hjSum)
              all_goals exact hJE ⟨⟩ mC rfl
          · c0_hfast; exact hJE ⟨⟩ mC rfl
      · intro JJ hJJ; c0_hfast; refine hJJ (s.qn.toNat - (i + 1#32).toNat)
          (_, _, i + 1#32, ⟨⟩) mC ⟨rfl, by omega, by omega, rfl, fun σ => ?_⟩
        simp only [bv64_zext32_toNat, hip1]
        exact CombineInv.hJ0_eval hh0_eq (by omega) hh0_ql hh0_qh hh0_unmod
    · have hi_eq : i.toNat = s.qn.toNat := by have := BitVec.not_lt.mp hc; omega
      clear hc
      have heval_done : ∀ σ : Nat → Bool,
          polyEvalIdxOf s.modW σ srcPool qm qlC qhC aC 0 k.toNat =
            polyEval s.modW σ srcPool qm ql qh s.qn.toNat := fun σ => by
        simpa [hi_eq, Nat.sub_self, polyEvalIdxOf_nil] using hevalC σ
      have hmC_base : (array64 s.ql qlC ⋆ array64 s.qh qhC ⋆ array (t := i32) sMid.ix aC ⋆
          (arCtxMem cx sMid ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
            array (t := i32) s.qm qm ⋆ array (t := i32) sMid.ix2 bArr ⋆ (restTQ ⋆ R))) mC := by
        dsimp only [Rcmb, Rcmb0] at hmC; rw [hRbase] at hmC; exact sep_cast hmC (by ac_rfl)
      have hm_ret := sort_combine_ret_mem rfl haC_len hptrs hfoc hmC_base
      c0_hfast; exact hQ k sMid qlC qhC aC bArr mC (by omega) hqlC_len hqhC_len
        (by omega) (by omega)
        (by rcases hptrs with ⟨ha, hb, hal, hbl⟩ | ⟨ha, hb, hal, hbl⟩ <;>
            simp [sMid, ha, hb, haC_len, hal, hbl])
        rfl hltA hndA heval_done hm_ret
  · intro JC hJC; c0_hfast; exact hJC s.qn.toNat (0#32, 0#32, ⟨⟩) _
      ⟨rfl, CombineInv.start hpermA (sep_cast hmMid (by dsimp only [Rcmb, Rcmb0]; ac_rfl))⟩

private theorem sort_combine_merge_phase (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X)
    {cx : Val i64} {Q : Post [i32]} {X : XPost} {s : ArCtxState}
    {tm0 tm1 : List (BitVec 32)} {ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)}
    {pool0 pool1 qm : List (BitVec 32)} {qs ql qh : List (BitVec 64)}
    {ix ix2 bx vqOff vq a2 : List (BitVec 32)} {vqSkip : List (BitVec 8)}
    {R restTQ Rbase : Mem 64 → Prop} {poolPtr : BitVec 64} {m2 : Mem 64}
    (hpc : s.pc.toNat < 2) (hqn_le : s.qn.toNat ≤ s.qcap.toNat)
    (hqcap32 : s.qcap.toNat + 16 < 2 ^ 32)
    (hqm_len : s.qcap.toNat ≤ qm.length) (hql_len : s.qcap.toNat ≤ ql.length)
    (hqh_len : s.qcap.toNat ≤ qh.length)
    (hix_len : s.qcap.toNat ≤ ix.length) (hix2_len : s.qcap.toNat ≤ ix2.length)
    (hMasks : MasksOk s.modW s.mlo s.mhi)
    (hQmOk : ∀ i < s.qn.toNat,
      MonoSliceOk (if s.pc.toNat = 0 then pool0 else pool1) (qm.getD i 0#32).toNat
        (if s.pc.toNat = 0 then pool0 else pool1).length ∧
      ((if s.pc.toNat = 0 then pool0 else pool1).getD
          (qm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hpool_eq : poolPtr = s.pool.getD s.pc.toNat 0#64)
    (hRbase : Rbase = restTQ ⋆ R)
    (hfoc : ∀ (s' : ArCtxState) (ql' qh' : List (BitVec 64)) (ix' ix2' : List (BitVec 32)),
      s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
      s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh → s'.bx = s.bx →
      s'.vq_off = s.vq_off → s'.vq = s.vq → s'.vq_skip = s.vq_skip →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧ ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
        (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧ ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          qMem s' qm qs ql' qh' ix' ix2' bx vqOff vq vqSkip =
        array (t := i32) (s.pool.getD s.pc.toNat 0#64)
          (if s.pc.toNat = 0 then pool0 else pool1) ⋆
        array (t := i32) s.qm qm ⋆ array64 s.ql ql' ⋆ array64 s.qh qh' ⋆
        array (t := i32) s'.ix ix' ⋆ array (t := i32) s'.ix2 ix2' ⋆ restTQ)
    (ha2_len : a2.length = ix.length) (hperm2 : PermN a2 s.qn.toNat)
    (hm2 : (arCtxMem cx s ⋆
      array (t := i32) (s.pool.getD s.pc.toNat 0#64) (if s.pc.toNat = 0 then pool0 else pool1) ⋆
      array (t := i32) s.qm qm ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
      array (t := i32) s.ix a2 ⋆ array (t := i32) s.ix2 ix2 ⋆ Rbase) m2)
    (hQ : ∀ (k : BitVec 32) (s' : ArCtxState) (ql' qh' : List (BitVec 64))
        (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
      k.toNat ≤ s.qn.toNat → ql'.length = ql.length → qh'.length = qh.length →
      s.qcap.toNat ≤ ix'.length → s.qcap.toNat ≤ ix2'.length →
      ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
        ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
       (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
        ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
      s' = { s with ix := s'.ix, ix2 := s'.ix2 } →
      (∀ p < k.toNat, (ix'.getD p 0#32).toNat < s.qn.toNat) →
      ((List.range k.toNat).map (fun p => (ix'.getD p 0#32).toNat)).Nodup →
      (∀ σ : Nat → Bool,
        polyEvalIdxOf s.modW σ (if s.pc.toNat = 0 then pool0 else pool1)
          qm ql' qh' ix' 0 k.toNat =
          polyEval s.modW σ (if s.pc.toNat = 0 then pool0 else pool1)
            qm ql qh s.qn.toNat) →
      (arCtxMem cx s' ⋆ tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s' qm qs ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆ R) m' → Q (k, ⟨⟩) m') :
    wp Γ Q X (sortCombineMergeExpr cx s.qn s.ix s.ix2 poolPtr s.qm) m2 := by
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  have hl_s : ArCtxLengthsOk s :=
    arCtxMem_lengths4 (sep_cast hm2 (by ac_rfl) :
      (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) s.qm qm ⋆
        (array64 s.ql ql ⋆ array64 s.qh qh ⋆ array (t := i32) s.ix a2 ⋆
          array (t := i32) s.ix2 ix2 ⋆ Rbase)) m2)
  have hpool_pc : poolPtr = s.pool.getD s.pc.toNat 0#64 := hpool_eq
  dsimp only [sortCombineMergeExpr]; c0_hfast
  obtain ⟨Rmerge, hRmerge⟩ : ∃ R0 : Mem 64 → Prop,
      R0 = arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
        array (t := i32) s.qm qm ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆ Rbase := ⟨_, rfl⟩
  refine wp_loop_group (MergeWInv s ix ix2 Rmerge) ?_ ?_
  · intro JW wrem ⟨aPtr, bPtr, w, ⟨⟩⟩ mW hrecW
      ⟨aArr, bArr, hptrs, hpermA, hw_lo, hw_bd, hwrem, hmW⟩
    have ha_qcap : s.qcap.toNat ≤ aArr.length ∧ s.qcap.toNat ≤ bArr.length := by
      rcases hptrs with ⟨_, _, ha, hb⟩ | ⟨_, _, ha, hb⟩ <;> omega
    c0_hsplit
    · have hw_lt : w.toNat < s.qn.toNat := hc
      clear hc
      have ⟨hw2_64, hw_shl, hw2_bd⟩ := merge_w_loop_bounds hw_lo hw_lt (by omega)
      c0_hfast_nogrp
      refine wp_loop_group (MergeLoInv aPtr bPtr aArr bArr s.qn.toNat w Rmerge) ?_ ?_
      · intro JL lorem ⟨lo, ⟨⟩⟩ mL hrecL ⟨bCur, hb_len, hlo_bd, hlorem, hprevL, hmL⟩
        clear hmW; c0_hsplit
        · have hlo_lt : lo.toNat < s.qn.toNat := hc
          clear hc
          have ⟨h64a, h64b, hmid_eq, hhi_eq⟩ := merge_slice_bounds hlo_lt hw_bd (by omega)
          have hlo32 : (lo.setWidth 32).toNat = lo.toNat := by
            have := s.qn.isLt; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          c0_hfast_nogrp
          refine wp_join_group (fun (v : Tup Val [i32]) mM1 =>
              mM1 = mL ∧ v.1.toNat = min (lo.toNat + w.toNat) s.qn.toNat) ?_ ?_
          · rintro J ⟨mid, ⟨⟩⟩ mM1 ⟨hmM1, hmid_v⟩; subst mM1
            have hmid_v' : mid.toNat = min (lo.toNat + w.toNat) s.qn.toNat := by
              simpa using hmid_v
            c0_hfast_nogrp
            refine wp_join_group (fun (v : Tup Val [i32]) mM2 =>
                mM2 = mL ∧ v.1.toNat = min (lo.toNat + 2 * w.toNat) s.qn.toNat) ?_ ?_
            · rintro J2 ⟨hi, ⟨⟩⟩ mM2 ⟨hmM2, hhi_v⟩; subst mM2
              have hhi_v' : hi.toNat = min (lo.toNat + 2 * w.toNat) s.qn.toNat := by
                simpa using hhi_v
              have hlo_mid : lo.toNat ≤ mid.toNat := by omega
              have hmid_hi : mid.toNat ≤ hi.toNat := by omega
              have hhi_qn : hi.toNat ≤ s.qn.toNat := by omega
              c0_hfast_nogrp
              refine wp_loop_group (MergeChunkLoopInv aPtr bPtr aArr bArr bCur
                  lo.toNat mid.toNat hi.toNat Rmerge) ?_ ?_
              · intro JM pqrem ⟨p, q, o, ⟨⟩⟩ mM hrecM ⟨hpqrem, bM, hbM_len, hlo_p, hp_mid,
                    hmid_q, hq_hi, ho_eq, hkeepM, hpermM, hmM⟩
                clear hmL
                refine wp_join_group (fun (_ : Tup Val []) mJ => mJ = mM) ?_ ?_
                · rintro JJ ⟨⟩ mJ hmJ; subst mJ; c0_hstraight
                  refine wp_loop_group (MergePInv aPtr bPtr aArr bArr bCur lo.toNat
                      mid.toNat hi.toNat q.toNat Rmerge) ?_ ?_
                  · intro JP prem ⟨p1, o1, ⟨⟩⟩ mP hrecP ⟨hprem, bP, hbP_len, hlo_p1,
                        hp1_mid, _, _, ho1_eq, hkeepP, hpermP, hmP⟩
                    clear hmM; c0_hsplit
                    · have hp1_lt : p1.toNat < mid.toNat := hc
                      clear hc
                      have ho1_p1 : (o1 + 1#32).toNat = o1.toNat + 1 :=
                        bv32_succ_toNat (by have := s.qn.isLt; omega)
                      have hp1_p1 : (p1 + 1#32).toNat = p1.toNat + 1 :=
                        bv32_succ_toNat (by have := s.qn.isLt; omega)
                      c0_hfast; exact hrecP (mid.toNat - (p1 + 1#32).toNat)
                        (p1 + 1#32, o1 + 1#32, ⟨⟩) _ (by rw [hp1_p1]; omega)
                        (sort_combine_jp_next hbP_len hlo_p1 hp1_lt hmid_q hq_hi ho1_eq
                          (by omega) (by omega) hkeepP hpermP ho1_p1 hp1_p1
                          (by simp only [bv64_zext32_toNat] at hm
                              exact sep_cast hm (by simp [ExtHashMap.sep_emp]; ac_rfl)))
                    · have hp1_eq : p1.toNat = mid.toNat := by have := BitVec.not_lt.mp hc; omega
                      clear hc; c0_hstraight
                      refine wp_loop_group (MergeQInv aPtr bPtr aArr bArr bCur
                          lo.toNat mid.toNat hi.toNat Rmerge) ?_ ?_
                      · intro JQ qrem ⟨q1, o2, ⟨⟩⟩ mQ hrecQ ⟨hqrem, bQ, hbQ_len, _, _,
                            hmid_q1, hq1_hi, ho2_eq, hkeepQ, hpermQ, hmQ⟩
                        clear hmP; c0_hsplit
                        · have hq1_lt : q1.toNat < hi.toNat := hc
                          clear hc
                          have ho2_p1 : (o2 + 1#32).toNat = o2.toNat + 1 :=
                            bv32_succ_toNat (by have := s.qn.isLt; omega)
                          have hq1_p1 : (q1 + 1#32).toNat = q1.toNat + 1 :=
                            bv32_succ_toNat (by have := s.qn.isLt; omega)
                          c0_hfast; exact hrecQ (hi.toNat - (q1 + 1#32).toNat)
                            (q1 + 1#32, o2 + 1#32, ⟨⟩) _ (by rw [hq1_p1]; omega)
                            (sort_combine_jq_next hbQ_len hlo_mid hmid_q1 hq1_lt ho2_eq
                              (by omega) (by omega) hkeepQ hpermQ ho2_p1 hq1_p1
                              (by simp only [bv64_zext32_toNat] at hm
                                  exact sep_cast hm (by simp [ExtHashMap.sep_emp]; ac_rfl)))
                        · have hq1_eq : q1.toNat = hi.toNat := by have := BitVec.not_lt.mp hc; omega
                          clear hc
                          have hlo2w := merge_lo2w_toNat h64b; c0_hfast
                          exact hrecL ((s.qn.toNat + 2 * w.toNat) - (lo + 2#64 * w).toNat)
                            (lo + 2#64 * w, ⟨⟩) mQ (by rw [hlo2w]; omega)
                            (sort_combine_lo_next hbQ_len h64b hlo_mid hmid_hi hhi_qn hhi_v
                              hprevL hkeepQ (by
                                rw [show o2.toNat = hi.toNat by omega, hq1_eq] at hpermQ
                                simpa [Nat.sub_self] using hpermQ) hmQ)
                      · intro JQ hJQ; c0_hfast; exact hJQ (hi.toNat - q.toNat)
                          (q, o1, ⟨⟩) mP ⟨rfl, bP, hbP_len, hlo_mid, le_refl _, hmid_q,
                            hq_hi, by omega, hkeepP, (by rw [hp1_eq] at hpermP; exact hpermP), hmP⟩
                  · intro JP hJP; c0_hfast; exact hJP (mid.toNat - p.toNat) (p, o, ⟨⟩) mM
                      ⟨rfl, bM, hbM_len, hlo_p, hp_mid, hmid_q, hq_hi, ho_eq, hkeepM, hpermM, hmM⟩
                · intro JJ hJJ; c0_hfast
                  · rename_i hc2
                    have hp_lt : p.toNat < mid.toNat := hc2
                    have hq_lt : q.toNat < hi.toNat := hc
                    try clear hc hc2
                    have ho_lt : o.toNat < bM.length := by omega
                    have ho_p1 : (o + 1#32).toNat = o.toNat + 1 :=
                      bv32_succ_toNat (by have := s.qn.isLt; omega)
                    have hp_p1 : (p + 1#32).toNat = p.toNat + 1 :=
                      bv32_succ_toNat (by have := s.qn.isLt; omega)
                    have hq_p1 : (q + 1#32).toNat = q.toNat + 1 :=
                      bv32_succ_toNat (by have := s.qn.isLt; omega)
                    have ha_p_lt := hpermA.mem_lt (by omega : p.toNat < s.qn.toNat)
                    have ha_q_lt := hpermA.mem_lt (by omega : q.toNat < s.qn.toNat)
                    have hp_qm' : (aArr[p.toNat]'(by omega)).toNat < qm.length := by
                      rw [← getD_eq_getElem aArr 0#32 (by omega)]; omega
                    have hq_qm' : (aArr[q.toNat]'(by omega)).toNat < qm.length := by
                      rw [← getD_eq_getElem aArr 0#32 (by omega)]; omega
                    rw [hRmerge] at hmM; c0_hstraight
                    let Rmc := arCtxMem cx s ⋆ array (t := i32) s.qm qm ⋆
                      array64 s.ql ql ⋆ array64 s.qh qh ⋆ array (t := i32) aPtr aArr ⋆
                      array (t := i32) bPtr bM ⋆ Rbase
                    have hmM' : (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
                        Rmc) mM := sep_cast hmM (by dsimp only [Rmc]; ac_rfl)
                    refine wp_call_of_spec _ _ (hMcmp _ _ _ _
                      ⟨s.pool.getD s.pc.toNat 0#64, srcPool,
                        (qm.getD (aArr.getD p.toNat 0#32).toNat 0#32).toNat,
                        (qm.getD (aArr.getD q.toNat 0#32).toNat 0#32).toNat, Rmc,
                        (by simp only [Arg.val]; rw [getD_eq_getElem aArr 0#32 (by omega)]
                            exact qm_pool_ptr_eq _ _ qm hp_qm' hpool_pc),
                        (by simp only [Arg.val]; rw [getD_eq_getElem aArr 0#32 (by omega)]
                            exact qm_pool_ptr_eq _ _ qm hq_qm' hpool_pc),
                        (hQmOk _ ha_p_lt).1, (hQmOk _ ha_q_lt).1, (hQmOk _ ha_p_lt).2, hmM',
                        fun cmp _ => ?_⟩)
                    · dsimp only [Rmc] at *; clear hmM'; rw [← hRmerge] at hmM
                      c0_hsplit
                      · clear hc; c0_hfast; exact hrecM ((hi.toNat - lo.toNat) -
                            ((o + 1#32).toNat - lo.toNat)) (p + 1#32, q, o + 1#32, ⟨⟩) _
                          (by rw [ho_p1]; omega) (sort_combine_jm_step_p hbM_len hlo_p hp_lt hmid_q
                            hq_hi ho_eq ho_lt (by omega) hkeepM hpermM ho_p1 hp_p1
                            (by simp only [bv64_zext32_toNat] at hm
                                exact sep_cast hm (by simp [ExtHashMap.sep_emp]; ac_rfl)))
                      · clear hc; c0_hfast; exact hrecM ((hi.toNat - lo.toNat) -
                            ((o + 1#32).toNat - lo.toNat)) (p, q + 1#32, o + 1#32, ⟨⟩) _
                          (by rw [ho_p1]; omega) (sort_combine_jm_step_q hbM_len hlo_p hp_mid hmid_q
                            hq_lt ho_eq ho_lt (by omega) hkeepM hpermM ho_p1 hq_p1
                            (by simp only [bv64_zext32_toNat] at hm
                                exact sep_cast hm (by simp [ExtHashMap.sep_emp]; ac_rfl)))
                  all_goals exact hJJ ⟨⟩ mM rfl
              · intro JM hJM; c0_hfast; exact hJM (hi.toNat - lo.toNat)
                  (lo.setWidth 32, mid, lo.setWidth 32, ⟨⟩) mL ⟨by rw [hlo32]; omega,
                    bCur, hb_len, by rw [hlo32]; exact le_refl _, by rw [hlo32]; exact hlo_mid,
                    le_refl _, hmid_hi, by rw [hlo32]; omega, fun t _ => rfl,
                    by simp only [hlo32, Nat.sub_self, List.range_zero,
                         List.map_nil, List.nil_append]
                       rw [show hi.toNat - lo.toNat =
                         (mid.toNat - lo.toNat) + (hi.toNat - mid.toNat) by omega,
                         List.range_add, List.map_append, List.map_map]
                       rw [show ((fun t => (aArr.getD (lo.toNat + t) 0#32).toNat) ∘
                           (fun x => mid.toNat - lo.toNat + x)) =
                           (fun x => (aArr.getD (mid.toNat + x) 0#32).toNat) by
                         funext x; dsimp; congr 2; omega],
                    hmL⟩
            · intro J2 hJ2; c0_hfast
              · have hlt : lo + 2#64 * w < BitVec.setWidth 64 s.qn := by
                  simpa [BitVec.lt_def, bv64_zext32_toNat] using hc
                exact hJ2 ((lo + 2#64 * w).setWidth 32, ⟨⟩) mL
                  ⟨rfl, by rw [← hhi_eq]; simp only [hlt, ↓reduceIte]⟩
              · have hlt : ¬ (lo + 2#64 * w < BitVec.setWidth 64 s.qn) := by
                  simpa [BitVec.lt_def, bv64_zext32_toNat] using hc
                exact hJ2 (s.qn, ⟨⟩) mL ⟨rfl, by rw [← hhi_eq]; simp only [hlt, ↓reduceIte]⟩
          · intro J hJ; c0_hfast
            · have hlt : lo + w < BitVec.setWidth 64 s.qn := by
                simpa [BitVec.lt_def, bv64_zext32_toNat] using hc
              exact hJ ((lo + w).setWidth 32, ⟨⟩) mL
                ⟨rfl, by rw [← hmid_eq]; simp only [hlt, ↓reduceIte]⟩
            · have hlt : ¬ (lo + w < BitVec.setWidth 64 s.qn) := by
                simpa [BitVec.lt_def, bv64_zext32_toNat] using hc
              exact hJ (s.qn, ⟨⟩) mL ⟨rfl, by rw [← hmid_eq]; simp only [hlt, ↓reduceIte]⟩
        · have hlo_qn : s.qn.toNat ≤ lo.toNat := by
            have hnot : ¬lo.toNat < (BitVec.setWidth 64 s.qn).toNat := by simpa using hc
            rw [bv64_zext32_toNat] at hnot; omega
          clear hc; c0_hfast
          exact hrecW (2 * max 16 s.qn.toNat - (w * 2#64).toNat) (bPtr, aPtr, w * 2#64, ⟨⟩) mL
            (by rw [show w * 2#64 = w <<< 1#64 by bv_omega]; omega)
            (by rw [show w * 2#64 = w <<< 1#64 by bv_omega]
                exact sort_combine_w_next hptrs hpermA hb_len hlo_qn hprevL hw_lo hw_shl hw2_bd hmL)
      · intro JL hJL; c0_hfast; exact hJL (s.qn.toNat + 2 * w.toNat) (0#64, ⟨⟩) mW
          ⟨bArr, rfl, by simp, rfl, by simp [Nat.min_eq_left (Nat.zero_le _)], hmW⟩
    · clear hc; rw [hRmerge] at hmW
      change wp Γ Q X (sortCombineCombineExpr cx s.qn s.ix s.ix2 poolPtr s.qm aPtr bPtr) mW
      exact sort_combine_combine_phase Γ hMcmp hCadd hpc hqn_le hqcap32 hqm_len hql_len hqh_len
        hix_len hix2_len hMasks hQmOk hpool_eq hRbase hfoc hptrs hpermA
        (sep_cast hmW (by ac_rfl)) hQ
  · intro JW hJW; c0_hfast; exact hJW (2 * max 16 s.qn.toNat - 16) (s.ix, s.ix2, 16#64, ⟨⟩) m2
      ⟨a2, ix2, Or.inl ⟨rfl, rfl, ha2_len, rfl⟩, hperm2, by decide,
        by simp [Nat.max_def]; split <;> omega, rfl,
        (by rw [hRmerge]; exact sep_cast hm2 (by ac_rfl))⟩

public theorem ar_sort_combine_wp (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    (hCadd : ∀ xs m Q X, arCaddSpec xs m Q X →
      Γ "ar_cadd" [i64, i64, i64, i64, i64] [i64, i64] xs m Q X) :
    ∀ xs m Q X, arSortCombineSpec xs m Q X → Func.wp Γ ar_sort_combine_body xs m Q X := by
  rintro ⟨cx, ⟨⟩⟩ m Q X
    ⟨s, tm0, tm1, ts0, tl0, th0, ts1, tl1, th1, pool0, pool1,
      qm, qs, ql, qh, ix, ix2, bx, vqOff, vq, vqSkip, R,
      hpc, hqn_le, hqcap32, hpool0_len, hpool1_len, hqm_len, hqs_len, hql_len, hqh_len,
      hix_len, hix2_len, hMasks, hQmOk, hm, hQ⟩
  let srcPool := if s.pc.toNat = 0 then pool0 else pool1
  have hsrcPool_len : s.pcap.toNat ≤ srcPool.length := by dsimp only [srcPool]; split <;> assumption
  obtain ⟨restTQ, hm_split, hfoc⟩ := tqMem_focus_ix s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1
    qm qs ql qh ix ix2 bx vqOff vq vqSkip hpc
  obtain ⟨Rbase, hRbase⟩ : ∃ R0 : Mem 64 → Prop, R0 = restTQ ⋆ R := ⟨_, rfl⟩
  have hl_s : ArCtxLengthsOk s := arCtxMem_lengths4 hm
  have hm0 : (arCtxMem cx s ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) s.qm qm ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
      array (t := i32) s.ix ix ⋆ array (t := i32) s.ix2 ix2 ⋆ Rbase) m := by
    have h' : ((tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip) ⋆ (arCtxMem cx s ⋆ R)) m :=
      sep_cast hm (by ac_rfl)
    rw [hm_split] at h'; rw [hRbase]; exact sep_cast h' (by dsimp only [srcPool]; ac_rfl)
  have hpool_pc : s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc) = s.pool.getD s.pc.toNat 0#64 :=
    (getD_eq_getElem s.pool 0#64 (by rw [hl_s.pool]; exact hpc)).symm
  obtain ⟨Rix, hRix⟩ : ∃ R0 : Mem 64 → Prop, R0 = arCtxMem cx s ⋆
      array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆ array (t := i32) s.qm qm ⋆
      array64 s.ql ql ⋆ array64 s.qh qh ⋆ array (t := i32) s.ix2 ix2 ⋆ Rbase := ⟨_, rfl⟩
  c0_hsteps; clear hm
  refine wp_loop_group (SortInitInv s ix Rix) ?_ ?_
  · intro J1 rem ⟨i, ⟨⟩⟩ m1 hrec1 ⟨a1, ha1_len, hi_le, hrem1, ha1_id, hm1⟩
    try clear hm0
    c0_hsplit
    · have hi_lt : i.toNat < s.qn.toNat := hc
      clear hc
      have hip1 : (i + 1#32).toNat = i.toNat + 1 := bv32_succ_toNat (by have := s.qn.isLt; omega)
      c0_hfast; exact hrec1 (s.qn.toNat - (i + 1#32).toNat) (i + 1#32, ⟨⟩) _ (by omega)
        ⟨a1.set i.toNat i, by simp [ha1_len], by omega, rfl,
          (by rw [hip1]; exact sort_combine_init_step ha1_id (by omega)), ‹_›⟩
    · have hi_eq : i.toNat = s.qn.toNat := by have := BitVec.not_lt.mp hc; omega
      clear hc
      have hperm1 : PermN a1 s.qn.toNat := permN_range_id (by simpa [hi_eq] using ha1_id)
      c0_hfast_nogrp; refine wp_loop_group (InsBlockInv s ix Rix) ?_ ?_
      · intro J2 irem ⟨i2, ⟨⟩⟩ m2 hrec2 ⟨a2, ha2_len, hperm2, hirem, hi2_bd, hm2⟩
        clear hm1; c0_hsplit
        · have hi2_lt : i2.toNat < s.qn.toNat := hc
          clear hc
          have hi2p16 : (i2 + 16#32).toNat = i2.toNat + 16 := by
            rw [BitVec.toNat_add, show (16#32 : BitVec 32).toNat = 16 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          c0_hstraight
          c0_join_ite (fun (v : Tup Val [i32]) m' =>
              m' = m2 ∧ v.1.toNat = min (i2.toNat + 16) s.qn.toNat)
          · rintro J ⟨e, ⟨⟩⟩ m' ⟨hm', he_val⟩; subst m'
            have he_val' : e.toNat = min (i2.toNat + 16) s.qn.toNat := by simpa using he_val
            have he_le : e.toNat ≤ s.qn.toNat := by rw [he_val']; exact Nat.min_le_right _ _
            have hi2p1 : (i2 + 1#32).toNat = i2.toNat + 1 :=
              bv32_succ_toNat (by have := s.qn.isLt; omega)
            c0_hfast_nogrp; refine wp_loop_group (InsJInv s ix i2 e Rix) ?_ ?_
            · intro J3 jrem ⟨j2, ⟨⟩⟩ m3 hrec3 ⟨a3, ha3_len, hperm3, hj_lo, hj_hi, hjrem, hm3⟩
              clear hm2; c0_hsplit
              · have hj_lt : j2.toNat < e.toNat := hc
                clear hc
                have hj_ix : j2.toNat < a3.length := by omega
                have hj_p1 : (j2 + 1#32).toNat = j2.toNat + 1 :=
                  bv32_succ_toNat (by have := s.qn.isLt; omega)
                c0_hfast_nogrp
                let x := a3[j2.toNat]'hj_ix
                have hx_lt : x.toNat < s.qn.toNat := by
                  dsimp only [x]; rw [← getD_eq_getElem a3 0#32 hj_ix]
                  exact hperm3.mem_lt (by omega)
                refine wp_loop_group (InsQInv s ix i2 j2 x Rix) ?_ ?_
                · intro J4 qrem ⟨q2, ⟨⟩⟩ m4 hrec4 ⟨a4, ha4_len, hq_lo, hq_hi, hqrem, hperm4, hm4⟩
                  clear hm3; c0_hfast
                  · have hq_gt : i2.toNat < q2.toNat := hc
                    have hqm1 : (q2 - 1#32).toNat = q2.toNat - 1 := by c0_bv_omega [hq_gt]
                    have hqm1_lt : q2.toNat - 1 < a4.length := by omega
                    have hq_lt : q2.toNat < a4.length := by omega
                    let vqm1 := a4[q2.toNat - 1]'hqm1_lt
                    have hv_lt : vqm1.toNat < s.qn.toNat :=
                      sort_combine_vqm1_lt hq_lt hqm1_lt (by omega) hperm4 (by omega)
                    have hv_idx : a4[(q2 - 1).toNat]'(by
                        rw [show (q2 - 1).toNat = q2.toNat - 1 from hqm1]; exact hqm1_lt) =
                        vqm1 := by
                      simp only [show (q2 - 1).toNat = q2.toNat - 1 from hqm1]; rfl
                    have hq_a_qm : (a4[(BitVec.setWidth 64 (q2 - 1)).toNat]'(by
                        rw [bv64_zext32_toNat]
                        have hsub : (q2 - 1).toNat = q2.toNat - 1 := hqm1
                        rw [hsub]; exact hqm1_lt)).toNat < qm.length := by
                      have hsub : (BitVec.setWidth 64 (q2 - 1)).toNat = q2.toNat - 1 := by
                        rw [bv64_zext32_toNat]; exact hqm1
                      have hv1 : a4[(BitVec.setWidth 64 (q2 - 1)).toNat]'(by
                          rw [hsub]; exact hqm1_lt) = vqm1 := by
                        simp only [hsub]; rfl
                      rw [hv1]; omega
                    have hx_j_qm : (a3[(BitVec.setWidth 64 j2).toNat]'(by
                        rw [bv64_zext32_toNat]; exact hj_ix)).toNat < qm.length := by
                      have hj1 : a3[(BitVec.setWidth 64 j2).toNat]'(by
                          rw [bv64_zext32_toNat]; exact hj_ix) = x := by
                        simp only [bv64_zext32_toNat]; rfl
                      rw [hj1]; omega
                    rw [hRix] at hm4; c0_hstraight
                    let Rmc := arCtxMem cx s ⋆ array (t := i32) s.qm qm ⋆ array64 s.ql ql ⋆
                      array64 s.qh qh ⋆ array (t := i32) s.ix a4 ⋆
                      array (t := i32) s.ix2 ix2 ⋆ Rbase
                    refine wp_call_of_spec _ _ (hMcmp _ _ _ _
                      ⟨s.pool.getD s.pc.toNat 0#64, srcPool,
                        (qm.getD vqm1.toNat 0#32).toNat, (qm.getD x.toNat 0#32).toNat, Rmc,
                        (by simp only [Arg.val, bv64_zext32_toNat, hv_idx]
                            exact qm_pool_ptr_eq _ _ qm (idx := vqm1.toNat) (by omega) hpool_pc),
                        (by simp only [Arg.val, bv64_zext32_toNat]
                            exact qm_pool_ptr_eq _ _ qm (idx := x.toNat) (by omega) hpool_pc),
                        (hQmOk _ hv_lt).1, (hQmOk _ hx_lt).1, (hQmOk _ hv_lt).2,
                        sep_cast hm4 (by dsimp only [Rmc]; ac_rfl), fun cmp _ => ?_⟩)
                    · rw [← hRix] at hm4; c0_hsplit
                      · clear hc; c0_hfast; exact hrec4 (q2.toNat - 1) (q2 - 1#32, ⟨⟩) _
                          (by omega) (sort_combine_ins_next ha4_len (by omega) (by omega) hq_hi
                            hq_gt hperm4 (by simp only [bv64_zext32_toNat, hv_idx] at hm; exact hm))
                      · clear hc; c0_hfast; exact hrec3 ((e.toNat + 1) - min (j2 + 1#32).toNat
                          (e.toNat + 1)) (j2 + 1#32, ⟨⟩) _ (by omega)
                          ⟨a4.set q2.toNat x, by simp [ha4_len], hperm4, by omega, by omega, rfl,
                            (by simp only [bv64_zext32_toNat] at hm; exact hm)⟩
                  · clear hc; have hq_lt : q2.toNat < a4.length := by omega
                    c0_hfast; exact hrec3 ((e.toNat + 1) - min (j2 + 1#32).toNat (e.toNat + 1))
                      (j2 + 1#32, ⟨⟩) _ (by omega) ⟨a4.set q2.toNat x, by simp [ha4_len], hperm4,
                        by omega, by omega, rfl, (by simp only [bv64_zext32_toNat] at hm; exact hm)⟩
                · intro J4 hJ4; c0_hfast; exact hJ4 j2.toNat (j2, ⟨⟩) m3 ⟨a3, ha3_len, by omega,
                    le_refl _, rfl, (by rw [List.set_getElem_self hj_ix]; exact hperm3), hm3⟩
              · clear hc; c0_hfast; exact hrec2 (s.qn.toNat - min (i2 + 16#32).toNat s.qn.toNat)
                  (i2 + 16#32, ⟨⟩) m3 (by omega) ⟨a3, ha3_len, hperm3, rfl, by omega, hm3⟩
            · intro J3 hJ3; c0_hfast
              exact hJ3 ((e.toNat + 1) - min (i2 + 1#32).toNat (e.toNat + 1))
                (i2 + 1#32, ⟨⟩) m2 ⟨a2, ha2_len, hperm2, by omega, by omega, rfl, hm2⟩
          · intro J hJ hlt16; dsimp only [Arg.val, liftCmp, lift2] at hlt16
            have hlt' := sort_combine_ins_hi (by c0_bv_omega [hi2_lt]) hlt16
            c0_hfast; exact hJ (s.qn, ⟨⟩) m2 ⟨rfl, by dsimp; exact hlt'⟩
          · intro J hJ hge16; dsimp only [Arg.val, liftCmp, lift2] at hge16
            have hge' := sort_combine_ins_hi (by c0_bv_omega [hi2_lt]) hge16
            simp only [Bool.false_eq_true, ↓reduceIte] at hge'
            c0_hfast; exact hJ (i2 + 16#32, ⟨⟩) m2 ⟨rfl, by rw [hi2p16]; omega⟩
        · clear hc; rw [hRix] at hm2
          change wp Γ Q X (sortCombineMergeExpr cx s.qn s.ix s.ix2
            (s.pool[s.pc.toNat]'(by rw [hl_s.pool]; exact hpc)) s.qm) m2
          exact sort_combine_merge_phase Γ hMcmp hCadd hpc hqn_le hqcap32 hqm_len hql_len hqh_len
            hix_len hix2_len hMasks hQmOk hpool_pc hRbase hfoc ha2_len hperm2
            (sep_cast hm2 (by dsimp only [srcPool]; ac_rfl)) hQ
      · intro J2 hJ2; c0_hfast; exact hJ2 s.qn.toNat (0#32, ⟨⟩) m1 ⟨a1, ha1_len, hperm1, rfl,
          by simp, hm1⟩
  · intro J1 hJ1; c0_hfast; exact hJ1 s.qn.toNat (0#32, ⟨⟩) m ⟨ix, rfl, Nat.zero_le _, rfl,
      fun t ht => by simp at ht, (by rw [hRix]; exact sep_cast hm0 (by ac_rfl))⟩


end LeanQbe.T.Examples.Arisca.Proof

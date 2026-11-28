/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly0
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Poly1 Pure Infrastructure, `PermN`, & `ar_gallop_wp` (`Arisca.Proof.Poly1Base`)

Pure specifications (`arSortCombineSpec`, `arGallopSpec`, `arMergeProductsSpec`),
`array64` WP load/store helpers, permutation/`nonBx` lemmas, `tqMem_focus_ix`,
`merge_chunk_perm`, and `ar_gallop_wp`.
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

@[expose] public section

/-! ## 1. Pure Predicates & Specifications (`Poly1`: `3` fns) -/

/-- `xs[0..n)` is a permutation of `0..n`. -/
def PermN (xs : List (BitVec 32)) (n : Nat) : Prop :=
  ((List.range n).map (fun i => (xs.getD i 0#32).toNat)).Perm (List.range n)

/-- `bx[0..nb)` is strictly increasing with all entries `< n`. -/
def strictIncBelow (bx : List (BitVec 32)) (nb n : Nat) : Prop :=
  (∀ p < nb, (bx.getD p 0#32).toNat < n) ∧
  (∀ p, p + 1 < nb → (bx.getD p 0#32).toNat < (bx.getD (p + 1) 0#32).toNat)

/-- Sum of `termEval` over `i ∈ [lo, lo + len)` excluding indices appearing in `bx[0..nb)`. -/
def nonBxRangeSum (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) (nb lo len : Nat) : BitVec nOut :=
  (List.range len).foldl (fun acc d =>
    let i := lo + d
    if (bx.take nb).any (fun x => x.toNat == i) then acc
    else acc + termEval nOut σ pool tm tl th i) 0#nOut

/-- Sum of non-`bx` terms in `[0, n)`. -/
def nonBxTermSum (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) (nb n : Nat) : BitVec nOut :=
  nonBxRangeSum nOut σ pool tm tl th bx nb 0 n

/-- Every symbol appearing in monomial slices `0 .. n - 1` has wire index `x / 2 < bd`. -/
def SymsBound (pool mOff : List (BitVec 32)) (n bd : Nat) : Prop :=
  ∀ i < n, ∀ x ∈ symListAt pool (mOff.getD i 0#32).toNat, x / 2 < bd

/-- WP specification for `ar_sort_combine(cx)`. -/
def arSortCombineSpec : Spec [i64] [i32] :=
  fun ⟨cx, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (tm0 tm1 : List (BitVec 32))
      (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 : List (BitVec 32))
      (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
      (R : Mem 64 → Prop),
      let srcPool := if s.pc.toNat = 0 then pool0 else pool1
      s.pc.toNat < 2 ∧
      s.qn.toNat ≤ s.qcap.toNat ∧ s.qcap.toNat + 16 < 2 ^ 32 ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      s.qcap.toNat ≤ qm.length ∧ s.qcap.toNat ≤ qs.length ∧
      s.qcap.toNat ≤ ql.length ∧ s.qcap.toNat ≤ qh.length ∧
      s.qcap.toNat ≤ ix.length ∧ s.qcap.toNat ≤ ix2.length ∧
      MasksOk s.modW s.mlo s.mhi ∧
      (∀ i < s.qn.toNat,
        MonoSliceOk srcPool (qm.getD i 0#32).toNat srcPool.length ∧
        (srcPool.getD (qm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (arCtxMem cx s ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m ∧
      (∀ (k : BitVec 32) (s' : ArCtxState) (ql' qh' : List (BitVec 64))
          (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
        k.toNat ≤ s.qn.toNat →
        ql'.length = ql.length → qh'.length = qh.length →
        s.qcap.toNat ≤ ix'.length → s.qcap.toNat ≤ ix2'.length →
        ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
          ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
         (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
          ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
        s' = { s with ix := s'.ix, ix2 := s'.ix2 } →
        (∀ p < k.toNat, (ix'.getD p 0#32).toNat < s.qn.toNat) →
        ((List.range k.toNat).map (fun p => (ix'.getD p 0#32).toNat)).Nodup →
        (∀ σ : Nat → Bool,
          polyEvalIdxOf s.modW σ srcPool qm ql' qh' ix' 0 k.toNat =
            polyEval s.modW σ srcPool qm ql qh s.qn.toNat) →
        (arCtxMem cx s' ⋆ tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          qMem s' qm qs ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆ R) m' →
        Q (k, ⟨⟩) m')

/-- WP specification for `ar_gallop(tm, pool, lo, n, q)`. -/
def arGallopSpec : Spec [i64, i64, i32, i32, i64] [i32] :=
  fun ⟨tmPtr, poolPtr, lo, n, qPtr, ⟨⟩⟩ m Q _ =>
    ∃ (tmArr poolArr : List (BitVec 32)) (qOff : Nat) (R : Mem 64 → Prop),
      lo.toNat ≤ n.toNat ∧ n.toNat ≤ tmArr.length ∧
      qPtr = poolPtr + BitVec.ofNat 64 (4 * qOff) ∧
      MonoSliceOk poolArr qOff poolArr.length ∧
      (poolArr.getD qOff 0#32).toNat + 1 < 2 ^ 32 ∧
      (∀ i < n.toNat,
        MonoSliceOk poolArr (tmArr.getD i 0#32).toNat poolArr.length ∧
        (poolArr.getD (tmArr.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (array (t := i32) tmPtr tmArr ⋆ array (t := i32) poolPtr poolArr ⋆ R) m ∧
      (∀ ret : BitVec 32, lo.toNat ≤ ret.toNat → ret.toNat ≤ n.toNat → Q (ret, ⟨⟩) m)

/-- WP specification for `ar_merge_products(cx, nb)`. -/
def arMergeProductsSpec : Spec [i64, i32] [] :=
  fun ⟨cx, nb, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (tm0 tm1 : List (BitVec 32))
      (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64)) (pool0 pool1 : List (BitVec 32))
      (qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
      (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
      (R : Mem 64 → Prop),
      let srcPool := if s.pc.toNat = 0 then pool0 else pool1
      let srcTm := if s.tc.toNat = 0 then tm0 else tm1
      let srcTs := if s.tc.toNat = 0 then ts0 else ts1
      s.pc.toNat < 2 ∧ s.tc.toNat < 2 ∧
      s.tn.toNat ≤ s.tcap.toNat ∧ s.qn.toNat ≤ s.qcap.toNat ∧
      s.ptop.toNat ≤ s.pcap.toNat ∧
      s.tcap.toNat < 2 ^ 30 ∧ s.qcap.toNat + 16 < 2 ^ 32 ∧
      (s.tn.toNat - nb.toNat) + s.qn.toNat ≤ s.tcap.toNat ∧
      nb.toNat ≤ s.tn.toNat ∧ nb.toNat ≤ bx.length ∧
      strictIncBelow bx nb.toNat s.tn.toNat ∧
      s.tcap.toNat ≤ tm0.length ∧ s.tcap.toNat ≤ tm1.length ∧
      s.tcap.toNat ≤ ts0.length ∧ s.tcap.toNat ≤ tl0.length ∧ s.tcap.toNat ≤ th0.length ∧
      s.tcap.toNat ≤ ts1.length ∧ s.tcap.toNat ≤ tl1.length ∧ s.tcap.toNat ≤ th1.length ∧
      s.pcap.toNat ≤ pool0.length ∧ s.pcap.toNat ≤ pool1.length ∧
      s.qcap.toNat ≤ qm.length ∧ s.qcap.toNat ≤ qs.length ∧
      s.qcap.toNat ≤ ql.length ∧ s.qcap.toNat ≤ qh.length ∧
      s.qcap.toNat ≤ ix.length ∧ s.qcap.toNat ≤ ix2.length ∧
      MasksOk s.modW s.mlo s.mhi ∧
      (∀ i < s.tn.toNat,
        MonoSliceOk srcPool (srcTm.getD i 0#32).toNat s.ptop.toNat ∧
        (srcPool.getD (srcTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (∀ i < s.qn.toNat,
        MonoSliceOk srcPool (qm.getD i 0#32).toNat s.ptop.toNat ∧
        (srcPool.getD (qm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
      (∀ i < s.tn.toNat, MonoSorted srcPool (srcTm.getD i 0#32).toNat) ∧
      (∀ i < s.qn.toNat, MonoSorted srcPool (qm.getD i 0#32).toNat) ∧
      SigOk srcPool srcTm srcTs s.tn.toNat ∧
      SigOk srcPool qm qs s.qn.toNat ∧
      (arCtxMem cx s ⋆ tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip ⋆ R) m ∧
      (∀ (s' : ArCtxState) (tm0' tm1' : List (BitVec 32))
          (ts0' tl0' th0' ts1' tl1' th1' ql' qh' : List (BitVec 64))
          (ix' ix2' : List (BitVec 32)) (m' : Mem 64),
        let srcTl := if s.tc.toNat = 0 then tl0 else tl1
        let srcTh := if s.tc.toNat = 0 then th0 else th1
        let dstTm := if s.tc.toNat = 0 then tm1' else tm0'
        let dstTs := if s.tc.toNat = 0 then ts1' else ts0'
        let dstTl := if s.tc.toNat = 0 then tl1' else tl0'
        let dstTh := if s.tc.toNat = 0 then th1' else th0'
        s'.tc.toNat = 1 - s.tc.toNat →
        s'.tn.toNat ≤ (s.tn.toNat - nb.toNat) + s.qn.toNat →
        s'.tn.toNat ≤ s.tcap.toNat →
        s' = { s with tc := s'.tc, tn := s'.tn, ix := s'.ix, ix2 := s'.ix2 } →
        tm0'.length = tm0.length → tm1'.length = tm1.length →
        ts0'.length = ts0.length → tl0'.length = tl0.length → th0'.length = th0.length →
        ts1'.length = ts1.length → tl1'.length = tl1.length → th1'.length = th1.length →
        ql'.length = ql.length → qh'.length = qh.length →
        ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧
          ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
         (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧
          ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
        s.qcap.toNat ≤ ix'.length → s.qcap.toNat ≤ ix2'.length →
        (if s.tc.toNat = 0 then tm0' = tm0 ∧ ts0' = ts0 ∧ tl0' = tl0 ∧ th0' = th0
          else tm1' = tm1 ∧ ts1' = ts1 ∧ tl1' = tl1 ∧ th1' = th1) →
        (∀ i < s'.tn.toNat,
          MonoSliceOk srcPool (dstTm.getD i 0#32).toNat s.ptop.toNat ∧
          (srcPool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) →
        (∀ i < s'.tn.toNat, MonoSorted srcPool (dstTm.getD i 0#32).toNat) →
        SigOk srcPool dstTm dstTs s'.tn.toNat →
        monoTotalWords srcPool dstTm s'.tn.toNat ≤
          monoTotalWords srcPool srcTm s.tn.toNat + monoTotalWords srcPool qm s.qn.toNat →
        (∀ bd : Nat, SymsBound srcPool srcTm s.tn.toNat bd →
          SymsBound srcPool qm s.qn.toNat bd → SymsBound srcPool dstTm s'.tn.toNat bd) →
        (∀ σ : Nat → Bool,
          polyEval s.modW σ srcPool dstTm dstTl dstTh s'.tn.toNat =
            nonBxTermSum s.modW σ srcPool srcTm srcTl srcTh bx nb.toNat s.tn.toNat +
              polyEval s.modW σ srcPool qm ql qh s.qn.toNat) →
        (arCtxMem cx s' ⋆ tMem s' tm0' tm1' ts0' tl0' th0' ts1' tl1' th1' pool0 pool1 ⋆
          qMem s' qm qs ql' qh' ix' ix2' bx vqOff vq vqSkip ⋆ R) m' →
        Q () m')

/-- Loop invariant for bottom-up merge of two adjacent slices `[lo, mid)` and `[mid, hi)`. -/
def MergeChunkInv (aPtr bPtr : BitVec 64) (aArr bArr bCur : List (BitVec 32))
    (lo mid hi p q o : Nat) (Rmerge : Mem 64 → Prop) (mM : Mem 64) : Prop :=
  ∃ bM : List (BitVec 32),
    bM.length = bArr.length ∧ lo ≤ p ∧ p ≤ mid ∧ mid ≤ q ∧ q ≤ hi ∧
    o = lo + (p - lo) + (q - mid) ∧
    (∀ t < lo, bM.getD t 0#32 = bCur.getD t 0#32) ∧
    ((List.range (o - lo)).map (fun t => (bM.getD (lo + t) 0#32).toNat) ++
      (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat) ++
      (List.range (hi - q)).map (fun t => (aArr.getD (q + t) 0#32).toNat)).Perm
      ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat)) ∧
    (array (t := i32) aPtr aArr ⋆ array (t := i32) bPtr bM ⋆ Rmerge) mM

/-- Loop invariant for deduplicating/combining sorted `ix[0..qn)` in `ar_sort_combine`. -/
def CombineInv (nOut : Nat) (srcPool qm : List (BitVec 32))
    (ql qh : List (BitVec 64)) (aArr : List (BitVec 32)) (qn : Nat)
    (qlPtr qhPtr ixPtr : BitVec 64) (Rcmb : Mem 64 → Prop) (k i : Nat) (mC : Mem 64) : Prop :=
  ∃ (qlC qhC : List (BitVec 64)) (aC : List (BitVec 32)),
    qlC.length = ql.length ∧ qhC.length = qh.length ∧ aC.length = aArr.length ∧
    k ≤ i ∧ i ≤ qn ∧
    (∀ p < k, ∃ idx < i, aC.getD p 0#32 = aArr.getD idx 0#32) ∧
    (∀ t, i ≤ t → t < qn → aC.getD t 0#32 = aArr.getD t 0#32) ∧
    ((List.range k).map (fun p => (aC.getD p 0#32).toNat)).Nodup ∧
    (∀ p < k, (aC.getD p 0#32).toNat < qn) ∧
    (∀ idx, (∀ p < k, (aC.getD p 0#32).toNat ≠ idx) →
      qlC.getD idx 0#64 = ql.getD idx 0#64 ∧ qhC.getD idx 0#64 = qh.getD idx 0#64) ∧
    (∀ σ : Nat → Bool,
      polyEvalIdxOf nOut σ srcPool qm qlC qhC aC 0 k +
        polyEvalIdxOf nOut σ srcPool qm ql qh aArr i (qn - i) =
        polyEval nOut σ srcPool qm ql qh qn) ∧
    (array64 qlPtr qlC ⋆ array64 qhPtr qhC ⋆ array (t := i32) ixPtr aC ⋆ Rcmb) mC

end

/-! ## 2. `array64` WP Helpers & Pure Permutation / `nonBx` Lemmas -/

public section

theorem wp_load_arr64_idx {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a : Arg Val i64} {k : Val i64 → Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 64)} {i : BitVec 32} {R : Mem 64 → Prop}
    (ha : a.val = base + BitVec.setWidth 64 i * 8)
    (hi : i.toNat < xs.length) (hm : (array64 base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[i.toNat])) m) : wp Γ Q X (.load i64 a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 (8 * i.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_comm i.toNat 8]
  exact head_wp_load ha' (loadVal_array64 hi hm) hk

theorem wp_store_arr64_idx {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {v : Arg Val i64} {a : Arg Val i64} {val : BitVec 64} {k : Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 64)} {idx : BitVec 32} {R : Mem 64 → Prop}
    (hv : v.val = val) (ha : a.val = base + BitVec.setWidth 64 idx * 8)
    (hi : idx.toNat < xs.length) (hm : (array64 base xs ⋆ R) m)
    (hk : ∀ m', (array64 base (xs.set idx.toNat val) ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 (8 * idx.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_comm idx.toNat 8]
  exact head_wp_store hv ha' (store_array64 val hi hm) hk

theorem PermN.mem_lt {xs : List (BitVec 32)} {n : Nat} (hp : PermN xs n)
    {i : Nat} (hi : i < n) : (xs.getD i 0#32).toNat < n := by
  have hm : (xs.getD i 0#32).toNat ∈ (List.range n).map (fun k => (xs.getD k 0#32).toNat) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  exact List.mem_range.mp (hp.subset hm)

theorem PermN.nodup {xs : List (BitVec 32)} {n : Nat} (hp : PermN xs n) :
    ((List.range n).map (fun i => (xs.getD i 0#32).toNat)).Nodup :=
  hp.nodup_iff.mpr List.nodup_range

theorem PermN.set_swap {xs : List (BitVec 32)} {n i j : Nat}
    (hp : PermN xs n) (hi : i < xs.length) (hj : j < xs.length)
    (hin : i < n) (hjn : j < n) (hij : i ≠ j) :
    PermN ((xs.set i (xs.getD j 0#32)).set j (xs.getD i 0#32)) n := by
  let f : Nat → Nat := fun k => (xs.getD k 0#32).toNat
  let g : Nat → Nat := fun k =>
    (((xs.set i (xs.getD j 0#32)).set j (xs.getD i 0#32)).getD k 0#32).toNat
  have hfg : ∀ k, g k = if k = j then f i else if k = i then f j else f k := by
    intro k
    dsimp only [g, f]
    rw [getD_set_eq (xs.set i (xs.getD j 0#32)) 0#32 _ (by simp [hj])]
    by_cases hkj : k = j
    · simp [hkj]
    · simp only [hkj, ↓reduceIte, getD_set_eq xs 0#32 _ hi]
      split <;> simp
  have hperm : ((List.range n).map g).Perm ((List.range n).map f) := by
    let base := ((List.range n).erase i).erase j
    have hi_mem : i ∈ List.range n := List.mem_range.mpr hin
    have hj_mem : j ∈ (List.range n).erase i :=
      (List.mem_erase_of_ne hij.symm).mpr (List.mem_range.mpr hjn)
    have hbase : (i :: j :: base).Perm (List.range n) := by
      have h1 : (j :: base).Perm ((List.range n).erase i) := (List.perm_cons_erase hj_mem).symm
      exact (List.Perm.cons i h1).trans (List.perm_cons_erase hi_mem).symm
    have hmem_base : ∀ k ∈ base, k ≠ i ∧ k ≠ j := by
      intro k hk
      have hk1 : k ∈ (List.range n).erase i := List.mem_of_mem_erase hk
      exact ⟨(List.nodup_range.mem_erase_iff.mp hk1).1,
        (List.Nodup.mem_erase_iff (List.nodup_range.erase i)).mp hk |>.1⟩
    have h1 := hbase.map g
    have h2 := hbase.map f
    have hswap : (g i :: g j :: base.map g).Perm (f i :: f j :: base.map f) := by
      have hgi : g i = f j := by rw [hfg, ite_eq_right hij, ite_eq_left rfl]
      have hgj : g j = f i := by rw [hfg, ite_eq_left rfl]
      have hbg : base.map g = base.map f := by
        apply List.map_congr_left
        intro k hk
        obtain ⟨hki, hkj⟩ := hmem_base k hk
        rw [hfg, ite_eq_right hkj, ite_eq_right hki]
      rw [hgi, hgj, hbg]
      exact List.Perm.swap (f i) (f j) (base.map f)
    exact (h1.symm.trans hswap).trans h2
  exact hperm.trans hp

theorem PermN.insert_shift {a4 : List (BitVec 32)} {n q : Nat} {x vqm1 : BitVec 32}
    (hq_gt : 0 < q) (hq_lt : q < a4.length) (hq_n : q < n)
    (hv : vqm1 = a4.getD (q - 1) 0#32)
    (hp : PermN (a4.set q x) n) :
    PermN ((a4.set q vqm1).set (q - 1) x) n := by
  have hsw := hp.set_swap (i := q - 1) (j := q) (by simp; omega)
    (by simp [hq_lt]) (by omega) hq_n (by omega)
  have hqx : (a4.set q x).getD q 0#32 = x := by
    rw [getD_set_eq a4 0#32 x hq_lt, ite_eq_left rfl]
  have heq : (((a4.set q x).set (q - 1) x).set q
      ((a4.set q x).getD (q - 1) 0#32)) = (a4.set q vqm1).set (q - 1) x := by
    apply List.ext_getElem
    · simp
    · intro idx h1 h2
      have hb1 : q - 1 < (a4.set q x).length := by simp; omega
      have hidx : idx < a4.length := by simpa using h2
      rw [← getD_eq_getElem _ 0#32 h1, ← getD_eq_getElem _ 0#32 h2,
        getD_set_eq _ 0#32 _ (by simp; exact hq_lt),
        getD_set_eq (a4.set q vqm1) 0#32 x (by simp; omega)]
      by_cases hqi : idx = q
      · simp only [hqi, ↓reduceIte]
        rw [getD_set_eq a4 0#32 x hq_lt, ite_eq_right (by omega),
          ite_eq_right (by omega), getD_set_eq a4 0#32 vqm1 hq_lt,
          ite_eq_left rfl, hv]
      · rw [ite_eq_right hqi, getD_set_eq (a4.set q x) 0#32 x hb1]
        by_cases hqm : idx = q - 1
        · simp only [hqm, ↓reduceIte]
        · simp only [hqm, ↓reduceIte, getD_set_eq a4 0#32 x hq_lt,
            getD_set_eq a4 0#32 vqm1 hq_lt, ite_eq_right hqi]
  rw [hqx] at hsw
  rwa [← heq]

theorem list_take_range_map {α : Type} (f : Nat → α) (a b : Nat) :
    (List.range (a + b)).map f =
      (List.range a).map f ++ (List.range b).map (fun t => f (a + t)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.map_singleton, ih,
      List.range_succ, List.map_append, List.map_singleton, List.append_assoc]

theorem list_perm_middle_move {α : Type} (l1 l2 l3 : List α) (x : α) :
    ((l1 ++ [x]) ++ l2 ++ l3).Perm (l1 ++ (x :: l2) ++ l3) := by
  simp [List.append_assoc]

theorem polyEvalIdxOf_split_one (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (ix : List (BitVec 32)) (lo n : Nat) :
    polyEvalIdxOf nOut σ pool mOff cl ch ix lo (n + 1) =
      termEval nOut σ pool mOff cl ch (ix.getD lo 0#32).toNat +
        polyEvalIdxOf nOut σ pool mOff cl ch ix (lo + 1) n := by
  have h := polyEvalIdxOf_add nOut σ pool mOff cl ch ix lo 1 n
  rw [Nat.add_comm 1 n] at h
  rw [h, polyEvalIdxOf_succ, polyEvalIdxOf_nil, BitVec.zero_add, Nat.add_zero]

theorem polyEvalIdxOf_congr_coeff {nOut : Nat} {σ : Nat → Bool}
    {pool mOff : List (BitVec 32)} {cl1 ch1 cl2 ch2 : List (BitVec 64)}
    {ix1 ix2 : List (BitVec 32)} {lo n : Nat}
    (hx : ∀ t < n, ix1.getD (lo + t) 0#32 = ix2.getD (lo + t) 0#32)
    (hc : ∀ t < n, let idx := (ix1.getD (lo + t) 0#32).toNat
      cl1.getD idx 0#64 = cl2.getD idx 0#64 ∧ ch1.getD idx 0#64 = ch2.getD idx 0#64) :
    polyEvalIdxOf nOut σ pool mOff cl1 ch1 ix1 lo n =
      polyEvalIdxOf nOut σ pool mOff cl2 ch2 ix2 lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [polyEvalIdxOf_succ, polyEvalIdxOf_succ,
      ih (fun t ht => hx t (Nat.lt_succ_of_lt ht)) (fun t ht => hc t (Nat.lt_succ_of_lt ht))]
    congr 1
    have hxn := hx n (Nat.lt_succ_self n)
    have hcn := hc n (Nat.lt_succ_self n)
    simp only [termEval, ← hxn, hcn.1, hcn.2]

theorem termEval_zero_coeff (nOut : Nat) (σ : Nat → Bool) (pool mOff : List (BitVec 32))
    (cl ch : List (BitVec 64)) (idx : Nat)
    (hl : cl.getD idx 0#64 = 0#64) (hh : ch.getD idx 0#64 = 0#64) :
    termEval nOut σ pool mOff cl ch idx = 0#nOut := by
  simp only [termEval, coeff128, hl, hh]; split <;> simp

theorem nonBxRangeSum_zero (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) (nb lo : Nat) :
    nonBxRangeSum nOut σ pool tm tl th bx nb lo 0 = 0#nOut := rfl

theorem nonBxRangeSum_succ (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) (nb lo len : Nat) :
    nonBxRangeSum nOut σ pool tm tl th bx nb lo (len + 1) =
      nonBxRangeSum nOut σ pool tm tl th bx nb lo len +
        (if (bx.take nb).any (fun x => x.toNat == lo + len) then 0#nOut
         else termEval nOut σ pool tm tl th (lo + len)) := by
  simp only [nonBxRangeSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  split <;> simp

theorem nonBxRangeSum_add (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) (nb lo a b : Nat) :
    nonBxRangeSum nOut σ pool tm tl th bx nb lo (a + b) =
      nonBxRangeSum nOut σ pool tm tl th bx nb lo a +
        nonBxRangeSum nOut σ pool tm tl th bx nb (lo + a) b := by
  induction b with
  | zero => simp [nonBxRangeSum_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, nonBxRangeSum_succ, nonBxRangeSum_succ, ih, BitVec.add_assoc,
      show lo + (a + b) = lo + a + b by omega]

theorem nonBxRangeSum_split_one (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) (nb lo len : Nat) :
    nonBxRangeSum nOut σ pool tm tl th bx nb lo (len + 1) =
      (if (bx.take nb).any (fun x => x.toNat == lo) then 0#nOut
       else termEval nOut σ pool tm tl th lo) +
      nonBxRangeSum nOut σ pool tm tl th bx nb (lo + 1) len := by
  have h := nonBxRangeSum_add nOut σ pool tm tl th bx nb lo 1 len
  rw [Nat.add_comm 1 len] at h
  rw [h, nonBxRangeSum_succ, nonBxRangeSum_zero, BitVec.zero_add, Nat.add_zero]

theorem strictIncBelow.any_eq {bx : List (BitVec 32)} {nb n bp cur : Nat}
    (hinc : strictIncBelow bx nb n) (hnb : nb ≤ bx.length)
    (hbp_le : bp ≤ nb) (hlo : ∀ p < bp, (bx.getD p 0#32).toNat < cur)
    (hhi : bp < nb → cur ≤ (bx.getD bp 0#32).toNat) :
    (bx.take nb).any (fun x => x.toNat == cur) =
      (bp < nb && (bx.getD bp 0#32).toNat == cur) := by
  have hmon : ∀ p q, p ≤ q → q < nb → (bx.getD p 0#32).toNat ≤ (bx.getD q 0#32).toNat := by
    intro p q hpq hq
    induction q with
    | zero => rw [show p = 0 by omega]; exact le_refl _
    | succ q ih =>
      by_cases hpeq : p = q + 1
      · rw [hpeq]; exact le_refl _
      · exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_of_lt (hinc.2 q hq))
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_iff_getElem, List.length_take, Nat.min_eq_left hnb,
    List.getElem_take, beq_iff_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hpeq⟩
    have hget : bx[p]'(by omega) = bx.getD p 0#32 := (getD_eq_getElem bx 0#32 (by omega)).symm
    rw [hget] at hpeq
    by_cases hpbp : p < bp
    · exact absurd (hpeq ▸ hlo p hpbp) (Nat.lt_irrefl _)
    · by_cases heq : p = bp
      · subst heq; exact ⟨decide_eq_true hp, hpeq⟩
      · have hlt : (bx.getD bp 0#32).toNat < (bx.getD p 0#32).toNat := by
          have h1 := hinc.2 bp (by omega)
          have h2 := hmon (bp + 1) p (by omega) hp
          omega
        have hle := hhi (by omega)
        omega
  · rintro ⟨hbp, hpeq⟩
    have hbp' : bp < nb := of_decide_eq_true hbp
    exact ⟨bx.getD bp 0#32, ⟨bp, hbp', (getD_eq_getElem bx 0#32 (by omega)).symm⟩, hpeq⟩

theorem nonBxRangeSum_eq_polyEval_of_none {nOut : Nat} {σ : Nat → Bool}
    {pool tm : List (BitVec 32)} {tl th : List (BitVec 64)}
    {bx : List (BitVec 32)} {nb lo len : Nat}
    (hnone : ∀ t < len, (bx.take nb).any (fun x => x.toNat == lo + t) = false) :
    nonBxRangeSum nOut σ pool tm tl th bx nb lo len =
      polyEvalRange nOut σ pool tm tl th lo len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [nonBxRangeSum_succ, polyEvalRange_succ, ih (fun t ht => hnone t (Nat.lt_succ_of_lt ht)),
      hnone len (Nat.lt_succ_self len)]
    rfl

private theorem list_nodup_filter {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp h
    simp only [List.filter_cons]
    split
    · exact List.nodup_cons.mpr
        ⟨fun hm => ha (List.mem_filter.mp hm).1, list_nodup_filter p hl⟩
    · exact list_nodup_filter p hl

private theorem list_perm_of_nodup_mem {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup → (∀ a, a ∈ xs ↔ a ∈ ys) → xs.Perm ys
  | [], ys, _, _, h => by
    cases ys with
    | nil => exact List.Perm.nil
    | cons y _ => exact absurd ((h y).mpr (List.Mem.head _)) (by simp)
  | x :: xs, ys, hx, hy, h => by
    obtain ⟨hx1, hx2⟩ := List.nodup_cons.mp hx
    have hxy : x ∈ ys := (h x).mp (List.Mem.head _)
    have hp := (List.perm_cons_erase hxy).symm
    refine (List.Perm.cons x ?_).trans hp
    apply list_perm_of_nodup_mem hx2 (hy.erase x)
    intro a
    by_cases hax : a = x
    · subst hax
      exact ⟨fun ha => absurd ha hx1,
        fun ha => absurd rfl ((List.Nodup.mem_erase_iff hy).mp ha).1⟩
    · simp only [List.mem_erase_of_ne hax, ← h a, List.mem_cons, hax, false_or]

private theorem list_perm_sum_nat {l1 l2 : List Nat} (hp : l1.Perm l2) : l1.sum = l2.sum := by
  induction hp with
  | nil => rfl
  | cons _ _ ih => simp [List.sum_cons, ih]
  | swap _ _ _ => simp [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem monoTotalWords_le_of_nodup {pool qm ix : List (BitVec 32)} {k qn : Nat}
    (hnd : ((List.range k).map (fun p => (ix.getD p 0#32).toNat)).Nodup)
    (hlt : ∀ p < k, (ix.getD p 0#32).toNat < qn) :
    (List.range k).foldl (fun acc p =>
      acc + ((pool.getD (qm.getD (ix.getD p 0#32).toNat 0#32).toNat 0#32).toNat + 1)) 0 ≤
      monoTotalWords pool qm qn := by
  let xs := (List.range k).map (fun p => (ix.getD p 0#32).toNat)
  let f : Nat → Nat := fun idx => (pool.getD (qm.getD idx 0#32).toNat 0#32).toNat + 1
  have hlhs : (List.range k).foldl (fun acc p =>
      acc + ((pool.getD (qm.getD (ix.getD p 0#32).toNat 0#32).toNat 0#32).toNat + 1)) 0 =
      (xs.map f).sum := by
    simp only [xs, f, List.foldl_map, List.sum_eq_foldl]
  have hrhs : monoTotalWords pool qm qn = ((List.range qn).map f).sum := by
    simp only [monoTotalWords, f, List.sum_eq_foldl, List.foldl_map]
  rw [hlhs, hrhs]
  let filt := (List.range qn).filter (fun idx => decide (idx ∈ xs))
  have hperm : xs.Perm filt := by
    apply list_perm_of_nodup_mem hnd (list_nodup_filter _ List.nodup_range)
    intro a
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro ha
      refine ⟨?_, ha⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact hlt p (List.mem_range.mp hp)
    · exact And.right
  rw [list_perm_sum_nat (hperm.map f)]
  suffices hsub : ∀ l : List Nat,
      ((l.filter (fun idx => decide (idx ∈ xs))).map f).sum ≤ (l.map f).sum from
    hsub (List.range qn)
  intro l
  induction l with
  | nil => simp
  | cons y ys ih =>
    simp only [List.filter_cons]
    split <;> simp [List.map_cons, List.sum_cons] <;> omega

theorem tqMem_focus_ix (s : ArCtxState)
    (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
    (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
    (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
    (hpc : s.pc.toNat < 2) :
    ∃ rest : Mem 64 → Prop,
      (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip =
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64)
            (if s.pc.toNat = 0 then pool0 else pool1) ⋆
         array (t := i32) s.qm qm ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
         array (t := i32) s.ix ix ⋆ array (t := i32) s.ix2 ix2 ⋆ rest)) ∧
      (∀ (s' : ArCtxState) (ql' qh' : List (BitVec 64)) (ix' ix2' : List (BitVec 32)),
        s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
        s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh →
        s'.bx = s.bx → s'.vq_off = s.vq_off → s'.vq = s.vq → s'.vq_skip = s.vq_skip →
        ((s'.ix = s.ix ∧ s'.ix2 = s.ix2 ∧ ix'.length = ix.length ∧ ix2'.length = ix2.length) ∨
         (s'.ix = s.ix2 ∧ s'.ix2 = s.ix ∧ ix'.length = ix2.length ∧ ix2'.length = ix.length)) →
        tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
          qMem s' qm qs ql' qh' ix' ix2' bx vqOff vq vqSkip =
          (array (t := i32) (s.pool.getD s.pc.toNat 0#64)
            (if s.pc.toNat = 0 then pool0 else pool1) ⋆
           array (t := i32) s.qm qm ⋆ array64 s.ql ql' ⋆ array64 s.qh qh' ⋆
           array (t := i32) s'.ix ix' ⋆ array (t := i32) s'.ix2 ix2' ⋆ rest)) := by
  have hpc' : s.pc = 0#32 ∨ s.pc = 1#32 := bv32_lt2_cases hpc
  have hu := arrayPad_u32_unfold
  rcases hpc' with h0 | h1
  · refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆ array64 (s.ts.getD 1 0#64) ts1 ⋆
      array64 (s.tl.getD 1 0#64) tl1 ⋆ array64 (s.th.getD 1 0#64) th1 ⋆
      arrayPad i32 (s.pool.getD 1 0#64) pool1 ⋆
      u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆ u32PadTail s.qm qm.length ⋆
      array64 s.qs qs ⋆ u32PadTail s.ix ix.length ⋆ u32PadTail s.ix2 ix2.length ⋆
      arrayPad i32 s.bx bx ⋆ arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆
      arrayPad i8 s.vq_skip vqSkip,
      by simp only [tMem, qMem, h0, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          ↓reduceIte, hu]; ac_rfl,
      fun s' ql' qh' ix' ix2' htm hts htl hth hpool hqm hqs hql hqh hbx hvqo hvq hvqs hix => by
        rcases hix with ⟨hi1, hi2, hl1, hl2⟩ | ⟨hi1, hi2, hl1, hl2⟩ <;>
        · simp only [tMem, qMem, h0, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
            ↓reduceIte, hu, htm, hts, htl, hth, hpool, hqm, hqs, hql, hqh, hbx, hvqo, hvq, hvqs,
            hi1, hi2, hl1, hl2]; ac_rfl⟩
  · refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆ array64 (s.ts.getD 1 0#64) ts1 ⋆
      array64 (s.tl.getD 1 0#64) tl1 ⋆ array64 (s.th.getD 1 0#64) th1 ⋆
      arrayPad i32 (s.pool.getD 0 0#64) pool0 ⋆
      u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆ u32PadTail s.qm qm.length ⋆
      array64 s.qs qs ⋆ u32PadTail s.ix ix.length ⋆ u32PadTail s.ix2 ix2.length ⋆
      arrayPad i32 s.bx bx ⋆ arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆
      arrayPad i8 s.vq_skip vqSkip,
      by simp only [tMem, qMem, h1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu]; ac_rfl,
      fun s' ql' qh' ix' ix2' htm hts htl hth hpool hqm hqs hql hqh hbx hvqo hvq hvqs hix => by
        rcases hix with ⟨hi1, hi2, hl1, hl2⟩ | ⟨hi1, hi2, hl1, hl2⟩ <;>
        · simp only [tMem, qMem, h1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
            show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu, htm, hts, htl, hth, hpool,
            hqm, hqs, hql, hqh, hbx, hvqo, hvq, hvqs, hi1, hi2, hl1, hl2]; ac_rfl⟩

theorem merge_chunk_perm {aArr bArr : List (BitVec 32)} {lo p q o mid hi : Nat}
    (_hlo : lo ≤ p) (_hp : p ≤ mid) (_hmid : mid ≤ q) (_hq : q ≤ hi)
    (_ho : o = lo + (p - lo) + (q - mid))
    (hperm : ((List.range (o - lo)).map (fun t => (bArr.getD (lo + t) 0#32).toNat) ++
      (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat) ++
      (List.range (hi - q)).map (fun t => (aArr.getD (q + t) 0#32).toNat)).Perm
      ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat))) :
    (p < mid → ∀ v, (v = (aArr.getD p 0#32).toNat) →
      ∀ b' : List (BitVec 32), (∀ t < o - lo, b'.getD (lo + t) 0#32 = bArr.getD (lo + t) 0#32) →
      (b'.getD o 0#32).toNat = v →
      ((List.range (o + 1 - lo)).map (fun t => (b'.getD (lo + t) 0#32).toNat) ++
        (List.range (mid - (p + 1))).map (fun t => (aArr.getD (p + 1 + t) 0#32).toNat) ++
        (List.range (hi - q)).map (fun t => (aArr.getD (q + t) 0#32).toNat)).Perm
        ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat))) ∧
    (q < hi → ∀ v, (v = (aArr.getD q 0#32).toNat) →
      ∀ b' : List (BitVec 32), (∀ t < o - lo, b'.getD (lo + t) 0#32 = bArr.getD (lo + t) 0#32) →
      (b'.getD o 0#32).toNat = v →
      ((List.range (o + 1 - lo)).map (fun t => (b'.getD (lo + t) 0#32).toNat) ++
        (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat) ++
        (List.range (hi - (q + 1))).map (fun t => (aArr.getD (q + 1 + t) 0#32).toNat)).Perm
        ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat))) := by
  constructor
  · intro hpm v hv b' hkeep hbo
    rw [show o + 1 - lo = (o - lo) + 1 by omega, List.range_succ, List.map_append,
      List.map_singleton, show lo + (o - lo) = o by omega, hbo, hv]
    have hcongr : (List.range (o - lo)).map (fun t => (b'.getD (lo + t) 0#32).toNat) =
        (List.range (o - lo)).map (fun t => (bArr.getD (lo + t) 0#32).toNat) := by
      apply List.map_congr_left; intro t ht; rw [hkeep t (List.mem_range.mp ht)]
    rw [hcongr]
    have hmp : mid - p = 1 + (mid - (p + 1)) := by omega
    have hcons : (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat) =
        (aArr.getD p 0#32).toNat ::
          (List.range (mid - (p + 1))).map (fun t => (aArr.getD (p + 1 + t) 0#32).toNat) := by
      rw [hmp, list_take_range_map (fun t => (aArr.getD (p + t) 0#32).toNat) 1 (mid - (p + 1))]
      simp [Nat.add_assoc]
    have hm := list_perm_middle_move
      ((List.range (o - lo)).map (fun t => (bArr.getD (lo + t) 0#32).toNat))
      ((List.range (mid - (p + 1))).map (fun t => (aArr.getD (p + 1 + t) 0#32).toNat))
      ((List.range (hi - q)).map (fun t => (aArr.getD (q + t) 0#32).toNat))
      (aArr.getD p 0#32).toNat
    rw [← hcons] at hm
    exact hm.trans hperm
  · intro hqh v hv b' hkeep hbo
    rw [show o + 1 - lo = (o - lo) + 1 by omega, List.range_succ, List.map_append,
      List.map_singleton, show lo + (o - lo) = o by omega, hbo, hv]
    have hcongr : (List.range (o - lo)).map (fun t => (b'.getD (lo + t) 0#32).toNat) =
        (List.range (o - lo)).map (fun t => (bArr.getD (lo + t) 0#32).toNat) := by
      apply List.map_congr_left; intro t ht; rw [hkeep t (List.mem_range.mp ht)]
    rw [hcongr]
    have hhq : hi - q = 1 + (hi - (q + 1)) := by omega
    have hcons : (List.range (hi - q)).map (fun t => (aArr.getD (q + t) 0#32).toNat) =
        (aArr.getD q 0#32).toNat ::
          (List.range (hi - (q + 1))).map (fun t => (aArr.getD (q + 1 + t) 0#32).toNat) := by
      rw [hhq, list_take_range_map (fun t => (aArr.getD (q + t) 0#32).toNat) 1 (hi - (q + 1))]
      simp [Nat.add_assoc]
    have hm : (((List.range (o - lo)).map (fun t => (bArr.getD (lo + t) 0#32).toNat) ++
        [(aArr.getD q 0#32).toNat]) ++
        (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat) ++
        (List.range (hi - (q + 1))).map (fun t => (aArr.getD (q + 1 + t) 0#32).toNat)).Perm
        ((List.range (o - lo)).map (fun t => (bArr.getD (lo + t) 0#32).toNat) ++
        (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat) ++
        ((aArr.getD q 0#32).toNat ::
          (List.range (hi - (q + 1))).map (fun t => (aArr.getD (q + 1 + t) 0#32).toNat))) := by
      let lb := (List.range (o - lo)).map (fun t => (bArr.getD (lo + t) 0#32).toNat)
      let lp := (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat)
      let lq := (List.range (hi - (q + 1))).map (fun t => (aArr.getD (q + 1 + t) 0#32).toNat)
      let x := (aArr.getD q 0#32).toNat
      have hp1 : ([x] ++ lp).Perm (lp ++ [x]) := List.perm_append_comm
      have hp2 : (lb ++ ([x] ++ lp) ++ lq).Perm (lb ++ (lp ++ [x]) ++ lq) :=
        List.Perm.append_right lq (List.Perm.append_left lb hp1)
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hp2
    rw [← hcons] at hm
    exact hm.trans hperm

theorem mergeChunkPerm_done {aArr bOut : List (BitVec 32)} {lo hi : Nat}
    (hlo_hi : lo ≤ hi)
    (hprev : ((List.range lo).map (fun t => (bOut.getD t 0#32).toNat)).Perm
      ((List.range lo).map (fun t => (aArr.getD t 0#32).toNat)))
    (hchunk : ((List.range (hi - lo)).map (fun t => (bOut.getD (lo + t) 0#32).toNat)).Perm
      ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat))) :
    ((List.range hi).map (fun t => (bOut.getD t 0#32).toNat)).Perm
      ((List.range hi).map (fun t => (aArr.getD t 0#32).toNat)) := by
  rw [show hi = lo + (hi - lo) by omega,
    list_take_range_map (fun t => (bOut.getD t 0#32).toNat) lo (hi - lo),
    list_take_range_map (fun t => (aArr.getD t 0#32).toNat) lo (hi - lo)]
  exact hprev.append hchunk

theorem combine_cadd_step {nOut : Nat} {σ : Nat → Bool}
    {pool qm : List (BitVec 32)} {ql0 qh0 : List (BitVec 64)} {a0 : List (BitVec 32)}
    {h0 : BitVec 32} {l h nl nh : BitVec 64} {j n : Nat} {S : BitVec nOut}
    (hjn : j < n)
    (hsym : symListAt pool (qm.getD (a0.getD j 0#32).toNat 0#32).toNat =
      symListAt pool (qm.getD h0.toNat 0#32).toNat)
    (hcadd : coeff128 nOut nl nh =
      coeff128 nOut l h + coeff128 nOut (ql0.getD (a0.getD j 0#32).toNat 0#64)
        (qh0.getD (a0.getD j 0#32).toNat 0#64))
    (hcur : (if monoValL σ (symListAt pool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
      polyEvalIdxOf nOut σ pool qm ql0 qh0 a0 j (n - j) = S) :
    (if monoValL σ (symListAt pool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut nl nh else 0#nOut) +
      polyEvalIdxOf nOut σ pool qm ql0 qh0 a0 (j + 1) (n - (j + 1)) = S := by
  have hsp : n - j = (n - (j + 1)) + 1 := by omega
  rw [hsp, polyEvalIdxOf_split_one] at hcur
  rw [← hcur]; clear hcur
  simp only [termEval, hsym]
  cases monoValL σ (symListAt pool (qm.getD h0.toNat 0#32).toNat)
  · simp [BitVec.zero_add]
  · simp only [↓reduceIte, hcadd]; rw [BitVec.add_assoc]

/-! ## 3. `ar_gallop_wp` -/

theorem ar_gallop_wp (Γ : T.Env)
    (hMcmp : ∀ xs m Q X, arMcmpSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X) :
    ∀ xs m Q X, arGallopSpec xs m Q X → Func.wp Γ ar_gallop_body xs m Q X := by
  rintro ⟨tmPtr, poolPtr, lo, n, qPtr, ⟨⟩⟩ m Q X
    ⟨tmArr, poolArr, qOff, R, hlo_le, hn_len, hqPtr, hqSlice, hqLt, hTmOk, hm, hQ⟩
  have hptr_eq : ∀ idx32 : BitVec 32,
      poolPtr + BitVec.setWidth 64 idx32 * 4 = poolPtr + BitVec.ofNat 64 (4 * idx32.toNat) := by
    intro idx32; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_comm _ 4]
  c0_hsteps
  refine wp_loop_group (fun rem ⟨base, step, ⟨⟩⟩ m' =>
      m' = m ∧ lo.toNat ≤ base.toNat ∧ base.toNat ≤ n.toNat ∧
      1 ≤ step.toNat ∧ step.toNat ≤ 2 * (n.toNat + 1) ∧
      rem = n.toNat - base.toNat)
    ?_ ?_
  · intro J rem ⟨base, step, ⟨⟩⟩ m' hrec ⟨hm_eq, hlo_b, hb_n, hstep1, hstep2, hrem⟩
    subst m'
    have hp_add : (base + step).toNat = base.toNat + step.toNat := by
      have := n.isLt; rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hp_nat : (base + step - 1#64).toNat = base.toNat + step.toNat - 1 := by
      have hle : (1#64 : BitVec 64).toNat ≤ (base + step).toNat := by
        rw [hp_add, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle), hp_add,
        show (1#64 : BitVec 64).toNat = 1 from rfl]
    try c0_hsteps
    · -- `p >= n` -> binary search `[base, n]`
      c0_hsteps
      refine wp_loop_group (fun lrem ⟨l, h, ⟨⟩⟩ m2 =>
          m2 = m ∧ lo.toNat ≤ l.toNat ∧ l.toNat ≤ h.toNat ∧ h.toNat ≤ n.toNat ∧
          lrem = h.toNat - l.toNat)
        ?_ ?_
      · intro J2 lrem ⟨l, h, ⟨⟩⟩ m2 hrec2 ⟨hm2, hlo_l, hl_h, hh_n, hlrem⟩
        subst m2
        try c0_hsteps
        · have hl_lt_h : l.toNat < h.toNat := hc
          have hmid_lt : (l + ((h - l) >>> 1#64)).toNat =
              l.toNat + (h.toNat - l.toNat) / 2 := by
            have h1 : (h - l).toNat = h.toNat - l.toNat := by c0_bv_omega [hl_lt_h]
            have h2 : ((h - l) >>> 1#64).toNat = (h.toNat - l.toNat) / 2 := by
              rw [bv_c0_toNat_ushiftRight_bv, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
                Nat.pow_one]
            have hhl : l.toNat + (h.toNat - l.toNat) / 2 < 2 ^ 64 := by
              have := n.isLt; omega
            rw [BitVec.toNat_add, h2, Nat.mod_eq_of_lt hhl]
          have hmid_n : (l + ((h - l) >>> 1#64)).toNat < n.toNat := by omega
          have hmid_tm : (l + ((h - l) >>> 1#64)).toNat < tmArr.length := by omega
          c0_hsteps
          have hmidOk := (hTmOk _ hmid_n).1
          have hmid_val : (tmArr[(l + ((h - l) >>> 1#64)).toNat]'hmid_tm).toNat =
              (tmArr.getD (l + ((h - l) >>> 1#64)).toNat 0#32).toNat := by
            rw [getD_eq_getElem tmArr 0#32 hmid_tm]
          refine wp_call_of_spec _ _ (hMcmp _ _ _ _
            ⟨poolPtr, poolArr, (tmArr.getD (l + ((h - l) >>> 1#64)).toNat 0#32).toNat,
              qOff, array (t := i32) tmPtr tmArr ⋆ R,
              ?_, ?_, hmidOk, hqSlice, (hTmOk _ hmid_n).2,
              sep_cast hm (by ac_rfl), fun cmp _ => ?_⟩)
          · dsimp only [Arg.val]; rw [← hmid_val]; exact hptr_eq _
          · dsimp only [Arg.val]; exact hqPtr
          · c0_hsteps
            · have hmidp1 : (l + ((h - l) >>> 1#64) + 1#64).toNat =
                  l.toNat + (h.toNat - l.toNat) / 2 + 1 := by
                have := n.isLt
                rw [BitVec.toNat_add, hmid_lt,
                  show (1#64 : BitVec 64).toNat = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]
              exact hrec2 (h.toNat - (l + ((h - l) >>> 1#64) + 1#64).toNat)
                (l + ((h - l) >>> 1#64) + 1#64, h, ⟨⟩) m (by omega)
                ⟨rfl, by omega, by omega, hh_n, rfl⟩
            · exact hrec2 (l.toNat + (h.toNat - l.toNat) / 2 - l.toNat)
                (l, l + ((h - l) >>> 1#64), ⟨⟩) m (by omega)
                ⟨rfl, hlo_l, by omega, by omega, by rw [hmid_lt]⟩
        · c0_hsteps
          have hl_ret : (l.setWidth 32).toNat = l.toNat := by
            have := n.isLt
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
          exact hQ (l.setWidth 32) (by omega) (by omega)
      · intro J2 hJ2
        c0_hsteps
        have hn64 : (n.setWidth 64).toNat = n.toNat := by
          have := n.isLt; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        exact hJ2 (n.toNat - base.toNat) (base, n.setWidth 64, ⟨⟩) m
          ⟨rfl, hlo_b, hb_n, by omega, by rw [hn64]⟩
    · -- `p < n`
      have hp_lt_n : (base + step - 1#64).toNat < n.toNat := by
        have := n.isLt
        have h1 : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + (base.toNat + step.toNat)) % 2 ^ 64 =
            base.toNat + step.toNat - 1 := by
          rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
        have hlt := Nat.lt_of_not_le hc
        rw [h1] at hlt; omega
      have hp_tm : (base + step - 1#64).toNat < tmArr.length := by omega
      c0_hsteps
      have hpOk := (hTmOk _ hp_lt_n).1
      have hp_val : (tmArr[(base + step - 1#64).toNat]'hp_tm).toNat =
          (tmArr.getD (base + step - 1#64).toNat 0#32).toNat := by
        rw [getD_eq_getElem tmArr 0#32 hp_tm]
      refine wp_call_of_spec _ _ (hMcmp _ _ _ _
        ⟨poolPtr, poolArr, (tmArr.getD (base + step - 1#64).toNat 0#32).toNat,
          qOff, array (t := i32) tmPtr tmArr ⋆ R,
          ?_, ?_, hpOk, hqSlice, (hTmOk _ hp_lt_n).2,
          sep_cast hm (by ac_rfl), fun cmp _ => ?_⟩)
      · dsimp only [Arg.val]; rw [← hp_val]; exact hptr_eq _
      · dsimp only [Arg.val]; exact hqPtr
      · c0_hsteps
        · have hp1 : (base + step - 1#64 + 1#64).toNat = base.toNat + step.toNat := by
            have := n.isLt
            rw [BitVec.toNat_add, hp_nat, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
            omega
          have hshl : (step <<< 1#64).toNat = 2 * step.toNat := by
            have := n.isLt
            rw [bv_c0_toNat_shiftLeft_bv, show (1#64 : BitVec 64).toNat = 1 from rfl,
              Nat.pow_one, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
          refine hrec (n.toNat - (base.toNat + step.toNat))
            (base + step - 1#64 + 1#64, step <<< 1#64, ⟨⟩) m (by omega)
            ⟨rfl, ?_⟩
          rw [hp1, hshl]
          exact ⟨by omega, by omega, by omega, by omega, rfl⟩
        · -- `!(cmp < 0)` -> binary search `[base, p]`
          c0_hsteps
          refine wp_loop_group (fun lrem ⟨l, h, ⟨⟩⟩ m2 =>
              m2 = m ∧ lo.toNat ≤ l.toNat ∧ l.toNat ≤ h.toNat ∧ h.toNat ≤ n.toNat ∧
              lrem = h.toNat - l.toNat)
            ?_ ?_
          · intro J2 lrem ⟨l, h, ⟨⟩⟩ m2 hrec2 ⟨hm2, hlo_l, hl_h, hh_n, hlrem⟩
            subst m2
            try c0_hsteps
            · have hl_lt_h : l.toNat < h.toNat := hc
              have hmid_lt : (l + ((h - l) >>> 1#64)).toNat =
                  l.toNat + (h.toNat - l.toNat) / 2 := by
                have h1 : (h - l).toNat = h.toNat - l.toNat := by c0_bv_omega [hl_lt_h]
                have h2 : ((h - l) >>> 1#64).toNat = (h.toNat - l.toNat) / 2 := by
                  rw [bv_c0_toNat_ushiftRight_bv, h1,
                    show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.pow_one]
                have hhl : l.toNat + (h.toNat - l.toNat) / 2 < 2 ^ 64 := by
                  have := n.isLt; omega
                rw [BitVec.toNat_add, h2, Nat.mod_eq_of_lt hhl]
              have hmid_n : (l + ((h - l) >>> 1#64)).toNat < n.toNat := by omega
              have hmid_tm : (l + ((h - l) >>> 1#64)).toNat < tmArr.length := by omega
              c0_hsteps
              have hmidOk := (hTmOk _ hmid_n).1
              have hmid_val : (tmArr[(l + ((h - l) >>> 1#64)).toNat]'hmid_tm).toNat =
                  (tmArr.getD (l + ((h - l) >>> 1#64)).toNat 0#32).toNat := by
                rw [getD_eq_getElem tmArr 0#32 hmid_tm]
              refine wp_call_of_spec _ _ (hMcmp _ _ _ _
                ⟨poolPtr, poolArr,
                  (tmArr.getD (l + ((h - l) >>> 1#64)).toNat 0#32).toNat,
                  qOff, array (t := i32) tmPtr tmArr ⋆ R,
                  ?_, ?_, hmidOk, hqSlice, (hTmOk _ hmid_n).2,
                  sep_cast hm (by ac_rfl), fun cmp _ => ?_⟩)
              · dsimp only [Arg.val]; rw [← hmid_val]; exact hptr_eq _
              · dsimp only [Arg.val]; exact hqPtr
              · c0_hsteps
                · have hmidp1 : (l + ((h - l) >>> 1#64) + 1#64).toNat =
                      l.toNat + (h.toNat - l.toNat) / 2 + 1 := by
                    have := n.isLt
                    rw [BitVec.toNat_add, hmid_lt,
                      show (1#64 : BitVec 64).toNat = 1 from rfl,
                      Nat.mod_eq_of_lt (by omega)]
                  exact hrec2 (h.toNat - (l + ((h - l) >>> 1#64) + 1#64).toNat)
                    (l + ((h - l) >>> 1#64) + 1#64, h, ⟨⟩) m (by omega)
                    ⟨rfl, by omega, by omega, hh_n, rfl⟩
                · exact hrec2 (l.toNat + (h.toNat - l.toNat) / 2 - l.toNat)
                    (l, l + ((h - l) >>> 1#64), ⟨⟩) m (by omega)
                    ⟨rfl, hlo_l, by omega, by omega, by rw [hmid_lt]⟩
            · c0_hsteps
              have hl_ret : (l.setWidth 32).toNat = l.toNat := by
                have := n.isLt
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              exact hQ (l.setWidth 32) (by omega) (by omega)
          · intro J2 hJ2
            c0_hsteps
            exact hJ2 ((base.toNat + step.toNat - 1) - base.toNat)
              (base, base + step - 1#64, ⟨⟩) m
              ⟨rfl, hlo_b, by omega, by omega, by rw [hp_nat]⟩
    · exact absurd hc (by decide)
  · intro J hJ
    c0_hsteps
    have hlo64 : (lo.setWidth 64).toNat = lo.toNat := by
      have := lo.isLt; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    have h1_64 : (1#64 : BitVec 64).toNat = 1 := rfl
    exact hJ (n.toNat - lo.toNat) (lo.setWidth 64, 1#64, ⟨⟩) m
      ⟨rfl, by rw [hlo64]; exact le_refl _, by rw [hlo64]; exact hlo_le,
        by rw [h1_64]; exact le_refl _, by rw [h1_64]; omega, by rw [hlo64]⟩

theorem arCtxMem_lengths {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) : ArCtxLengthsOk s := by
  unfold arCtxMem at hm
  exact (sep_pure_l.mp hm).1

theorem arCtxMem_lengths4 {cx : BitVec 64} {s : ArCtxState} {A B C : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ A ⋆ B ⋆ C) m) : ArCtxLengthsOk s :=
  arCtxMem_lengths (sep_cast hm (by ac_rfl) : (arCtxMem cx s ⋆ (A ⋆ B ⋆ C)) m)

theorem qm_pool_ptr_eq (poolBase poolIdx : BitVec 64) (qm : List (BitVec 32))
    {idx : Nat} (hidx : idx < qm.length) (hpb : poolBase = poolIdx) :
    poolBase + BitVec.setWidth 64 (qm[idx]'hidx) * 4 =
      poolIdx + BitVec.ofNat 64 (4 * (qm.getD idx 0#32).toNat) := by
  rw [hpb, getD_eq_getElem qm 0#32 hidx]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, Nat.mul_comm _ 4]

theorem bv32_succ_toNat {v : BitVec 32} (hv : v.toNat + 1 < 2 ^ 32) :
    (v + 1#32).toNat = v.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt hv]

theorem permN_range_id {a1 : List (BitVec 32)} {n : Nat}
    (ha : ∀ t < n, (a1.getD t 0#32).toNat = t) : PermN a1 n := by
  unfold PermN
  have hmap : (List.range n).map (fun t => (a1.getD t 0#32).toNat) = (List.range n).map id :=
    List.map_congr_left (fun t ht => ha t (List.mem_range.mp ht))
  rw [hmap, List.map_id]

theorem nodup_getElem_inj {l : List Nat} (hnd : l.Nodup) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (heq : l[i] = l[j]) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact absurd (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)) hnd.1
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_succ, List.getElem_cons_zero] at heq
        exact absurd (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)) hnd.1
      | succ j' =>
        simp only [List.getElem_cons_succ] at heq
        exact congrArg Nat.succ
          (ih hnd.2 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

theorem ins_e_val {qn i2 : BitVec 32} (hi2_lt : i2.toNat < qn.toNat)
    (hi2p16 : i2.toNat + 16 < 2 ^ 32) :
    (if (qn - i2) < 16#32 then qn else i2 + 16#32).toNat =
      min (i2.toNat + 16) qn.toNat := by
  have hsub : (qn - i2).toNat = qn.toNat - i2.toNat := by c0_bv_omega [hi2_lt]
  have hadd : (i2 + 16#32).toNat = i2.toNat + 16 := by
    rw [BitVec.toNat_add, show (16#32 : BitVec 32).toNat = 16 from rfl, Nat.mod_eq_of_lt hi2p16]
  by_cases h : (qn - i2) < 16#32
  · have hlt : qn.toNat - i2.toNat < 16 := by
      simpa [BitVec.lt_def, hsub, show (16#32 : BitVec 32).toNat = 16 from rfl] using h
    simp only [h, ↓reduceIte]; omega
  · have hge : ¬ qn.toNat - i2.toNat < 16 := by
      simpa [BitVec.lt_def, hsub, show (16#32 : BitVec 32).toNat = 16 from rfl] using h
    simp only [h, ↓reduceIte, hadd]; omega

theorem merge_w_loop_bounds {qn : BitVec 32} {w : BitVec 64}
    (hw_lo : 16 ≤ w.toNat) (hw_lt : w.toNat < qn.toNat) (hq32 : qn.toNat + 16 < 2 ^ 32) :
    2 * w.toNat < 2 ^ 64 ∧ (w <<< 1#64).toNat = 2 * w.toNat ∧
      (w <<< 1#64).toNat ≤ 2 * max 16 qn.toNat := by
  have hlt : 2 * w.toNat < 2 ^ 64 := by omega
  have h1 : (w <<< 1#64).toNat = 2 * w.toNat := by
    rw [bv_c0_toNat_shiftLeft_bv, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.pow_one, Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  exact ⟨hlt, h1, by omega⟩

theorem merge_slice_bounds {qn : BitVec 32} {lo w : BitVec 64}
    (hlo_lt : lo.toNat < qn.toNat) (hw_bd : w.toNat ≤ 2 * max 16 qn.toNat)
    (hq32 : qn.toNat + 16 < 2 ^ 32) :
    lo.toNat + w.toNat < 2 ^ 64 ∧ lo.toNat + 2 * w.toNat < 2 ^ 64 ∧
      ((if lo + w < qn.setWidth 64 then (lo + w).setWidth 32 else qn).toNat =
        min (lo.toNat + w.toNat) qn.toNat) ∧
      ((if lo + 2#64 * w < qn.setWidth 64 then (lo + 2#64 * w).setWidth 32 else qn).toNat =
        min (lo.toNat + 2 * w.toNat) qn.toNat) := by
  have h64a : lo.toNat + w.toNat < 2 ^ 64 := by omega
  have h64b : lo.toNat + 2 * w.toNat < 2 ^ 64 := by omega
  have hq64 : (qn.setWidth 64).toNat = qn.toNat := by
    have := qn.isLt; rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hadd1 : (lo + w).toNat = lo.toNat + w.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt h64a]
  have hadd2 : (lo + 2#64 * w).toNat = lo.toNat + 2 * w.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, show (2#64 : BitVec 64).toNat = 2 from rfl,
      Nat.mod_eq_of_lt (by omega : 2 * w.toNat < 2 ^ 64), Nat.mod_eq_of_lt h64b]
  refine ⟨h64a, h64b, ?_, ?_⟩
  · by_cases h : lo + w < qn.setWidth 64
    · have hlt : lo.toNat + w.toNat < qn.toNat := by simpa [BitVec.lt_def, hadd1, hq64] using h
      simp only [h, ↓reduceIte, BitVec.toNat_setWidth, hadd1]; omega
    · have hge : ¬ lo.toNat + w.toNat < qn.toNat := by simpa [BitVec.lt_def, hadd1, hq64] using h
      simp only [h, ↓reduceIte]; omega
  · by_cases h : lo + 2#64 * w < qn.setWidth 64
    · have hlt : lo.toNat + 2 * w.toNat < qn.toNat := by
        simpa [BitVec.lt_def, hadd2, hq64] using h
      simp only [h, ↓reduceIte, BitVec.toNat_setWidth, hadd2]; omega
    · have hge : ¬ lo.toNat + 2 * w.toNat < qn.toNat := by
        simpa [BitVec.lt_def, hadd2, hq64] using h
      simp only [h, ↓reduceIte]; omega

theorem MergeChunkInv.step_p {aPtr bPtr : BitVec 64}
    {aArr bArr bCur bM : List (BitVec 32)} {lo mid hi p q o : Nat}
    {Rmerge : Mem 64 → Prop} {m' : Mem 64}
    (hb_len : bM.length = bArr.length) (hlo_p : lo ≤ p) (hp_lt : p < mid)
    (hmid_q : mid ≤ q) (hq_hi : q ≤ hi)
    (ho_eq : o = lo + (p - lo) + (q - mid)) (ho_lt : o < bM.length) (hp_lt_a : p < aArr.length)
    (hkeep : ∀ t < lo, bM.getD t 0#32 = bCur.getD t 0#32)
    (hperm : ((List.range (o - lo)).map (fun t => (bM.getD (lo + t) 0#32).toNat) ++
      (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat) ++
      (List.range (hi - q)).map (fun t => (aArr.getD (q + t) 0#32).toNat)).Perm
      ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat)))
    (hm' : (array (t := i32) aPtr aArr ⋆
      array (t := i32) bPtr (bM.set o (aArr[p]'hp_lt_a)) ⋆ Rmerge) m') :
    MergeChunkInv aPtr bPtr aArr bArr bCur lo mid hi (p + 1) q (o + 1) Rmerge m' := by
  let b' := bM.set o (aArr[p]'hp_lt_a)
  have hp_step := (merge_chunk_perm hlo_p (Nat.le_of_lt hp_lt) hmid_q hq_hi ho_eq hperm).1
    hp_lt (aArr.getD p 0#32).toNat (by rw [getD_eq_getElem aArr 0#32 hp_lt_a]) b'
    (fun t ht => by
      dsimp only [b']; rw [getD_set_eq bM 0#32 _ ho_lt]
      by_cases hto : lo + t = o
      · omega
      · simp only [hto, ↓reduceIte])
    (by
      dsimp only [b']; rw [getD_set_eq bM 0#32 _ ho_lt, ← getD_eq_getElem aArr 0#32 hp_lt_a]
      simp)
  exact ⟨b', by simp [b', hb_len], by omega, hp_lt, hmid_q, hq_hi, by omega,
    fun t ht => by
      dsimp only [b']; rw [getD_set_eq bM 0#32 _ ho_lt]
      by_cases hto : t = o
      · omega
      · simp only [hto, ↓reduceIte]; exact hkeep t ht,
    hp_step, hm'⟩

theorem MergeChunkInv.step_q {aPtr bPtr : BitVec 64}
    {aArr bArr bCur bM : List (BitVec 32)} {lo mid hi p q o : Nat}
    {Rmerge : Mem 64 → Prop} {m' : Mem 64}
    (hb_len : bM.length = bArr.length) (hlo_p : lo ≤ p) (hp_mid : p ≤ mid)
    (hmid_q : mid ≤ q) (hq_lt : q < hi)
    (ho_eq : o = lo + (p - lo) + (q - mid)) (ho_lt : o < bM.length) (hq_lt_a : q < aArr.length)
    (hkeep : ∀ t < lo, bM.getD t 0#32 = bCur.getD t 0#32)
    (hperm : ((List.range (o - lo)).map (fun t => (bM.getD (lo + t) 0#32).toNat) ++
      (List.range (mid - p)).map (fun t => (aArr.getD (p + t) 0#32).toNat) ++
      (List.range (hi - q)).map (fun t => (aArr.getD (q + t) 0#32).toNat)).Perm
      ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat)))
    (hm' : (array (t := i32) aPtr aArr ⋆
      array (t := i32) bPtr (bM.set o (aArr[q]'hq_lt_a)) ⋆ Rmerge) m') :
    MergeChunkInv aPtr bPtr aArr bArr bCur lo mid hi p (q + 1) (o + 1) Rmerge m' := by
  let b' := bM.set o (aArr[q]'hq_lt_a)
  have hq_step := (merge_chunk_perm hlo_p hp_mid hmid_q (Nat.le_of_lt hq_lt) ho_eq hperm).2
    hq_lt (aArr.getD q 0#32).toNat (by rw [getD_eq_getElem aArr 0#32 hq_lt_a]) b'
    (fun t ht => by
      dsimp only [b']; rw [getD_set_eq bM 0#32 _ ho_lt]
      by_cases hto : lo + t = o
      · omega
      · simp only [hto, ↓reduceIte])
    (by
      dsimp only [b']; rw [getD_set_eq bM 0#32 _ ho_lt, ← getD_eq_getElem aArr 0#32 hq_lt_a]
      simp)
  exact ⟨b', by simp [b', hb_len], hlo_p, hp_mid, by omega, hq_lt, by omega,
    fun t ht => by
      dsimp only [b']; rw [getD_set_eq bM 0#32 _ ho_lt]
      by_cases hto : t = o
      · omega
      · simp only [hto, ↓reduceIte]; exact hkeep t ht,
    hq_step, hm'⟩

theorem merge_lo_next_perm {aArr bArr bOut : List (BitVec 32)} {lo mid hi qn w : Nat}
    (hlo_hi : lo ≤ hi) (hlo_qn : lo ≤ qn) (hhi_eq : hi = min (lo + 2 * w) qn)
    (hprev : ((List.range (min lo qn)).map (fun t => (bArr.getD t 0#32).toNat)).Perm
      ((List.range (min lo qn)).map (fun t => (aArr.getD t 0#32).toNat)))
    (hkeep : ∀ t < lo, bOut.getD t 0#32 = bArr.getD t 0#32)
    (hchunk : ((List.range (hi - lo)).map (fun t => (bOut.getD (lo + t) 0#32).toNat) ++
      (List.range (mid - mid)).map (fun t => (aArr.getD (mid + t) 0#32).toNat) ++
      (List.range (hi - hi)).map (fun t => (aArr.getD (hi + t) 0#32).toNat)).Perm
      ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat))) :
    ((List.range (min (lo + 2 * w) qn)).map (fun t => (bOut.getD t 0#32).toNat)).Perm
      ((List.range (min (lo + 2 * w) qn)).map (fun t => (aArr.getD t 0#32).toNat)) := by
  rw [← hhi_eq]
  rw [Nat.min_eq_left hlo_qn] at hprev
  have hprev' : ((List.range lo).map (fun t => (bOut.getD t 0#32).toNat)).Perm
      ((List.range lo).map (fun t => (aArr.getD t 0#32).toNat)) := by
    have heq : (List.range lo).map (fun t => (bOut.getD t 0#32).toNat) =
        (List.range lo).map (fun t => (bArr.getD t 0#32).toNat) := by
      apply List.map_congr_left; intro t ht; rw [hkeep t (List.mem_range.mp ht)]
    rwa [heq]
  have hc : ((List.range (hi - lo)).map (fun t => (bOut.getD (lo + t) 0#32).toNat)).Perm
      ((List.range (hi - lo)).map (fun t => (aArr.getD (lo + t) 0#32).toNat)) := by
    simpa [Nat.sub_self] using hchunk
  exact mergeChunkPerm_done hlo_hi hprev' hc

theorem combine_idx_unmod {aFinal aCur : List (BitVec 32)}
    {ql qlCur qh qhCur : List (BitVec 64)} {n k i t : Nat}
    (hpermF : PermN aFinal n) (ht_lt : t < n)
    (hsrc_a : ∀ p < k, ∃ idx < i, aCur.getD p 0#32 = aFinal.getD idx 0#32) (hne_range : i ≤ t)
    (hql_unmod : ∀ idx, (∀ p < k, (aCur.getD p 0#32).toNat ≠ idx) →
      qlCur.getD idx 0#64 = ql.getD idx 0#64 ∧ qhCur.getD idx 0#64 = qh.getD idx 0#64) :
    qlCur.getD (aFinal.getD t 0#32).toNat 0#64 = ql.getD (aFinal.getD t 0#32).toNat 0#64 ∧
    qhCur.getD (aFinal.getD t 0#32).toNat 0#64 = qh.getD (aFinal.getD t 0#32).toNat 0#64 := by
  apply hql_unmod; intro p hp heq
  obtain ⟨idx, hidx, heqp⟩ := hsrc_a p hp
  have heqF : (aFinal.getD idx 0#32).toNat = (aFinal.getD t 0#32).toNat := by rw [← heqp, heq]
  have hc := nodup_getElem_inj hpermF.nodup (by simp; omega : idx < _) (by simp; omega : t < _)
    (by simpa [show idx < n by omega, ht_lt] using heqF)
  omega

theorem combine_emit_ok {nOut : Nat}
    {srcPool qm : List (BitVec 32)} {ql qlCur qh qhCur : List (BitVec 64)}
    {aFinal aCur : List (BitVec 32)} {n k i j : Nat} {h0 : BitVec 32} {l h : BitVec 64}
    (_hk_le : k ≤ i) (hi_lt : i < n) (hj_lo : i + 1 ≤ j) (hj_le : j ≤ n)
    (hh0 : h0 = aFinal.getD i 0#32) (hpermF : PermN aFinal n)
    (hl_cur : qlCur.length = ql.length) (hh_cur : qhCur.length = qh.length)
    (hqn_ql : n ≤ ql.length) (hqn_qh : n ≤ qh.length)
    (hsrc_a : ∀ p < k, ∃ idx < i, aCur.getD p 0#32 = aFinal.getD idx 0#32)
    (hrest_a : ∀ t, i ≤ t → t < n → aCur.getD t 0#32 = aFinal.getD t 0#32)
    (hnd_a : ((List.range k).map (fun p => (aCur.getD p 0#32).toNat)).Nodup)
    (hlt_a : ∀ p < k, (aCur.getD p 0#32).toNat < n)
    (hql_unmod : ∀ idx, (∀ p < k, (aCur.getD p 0#32).toNat ≠ idx) →
      qlCur.getD idx 0#64 = ql.getD idx 0#64 ∧ qhCur.getD idx 0#64 = qh.getD idx 0#64)
    (hsum : ∀ σ : Nat → Bool,
      (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
      polyEvalIdxOf nOut σ srcPool qm ql qh aFinal j (n - j) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aFinal i (n - i))
    (heval_old : ∀ σ : Nat → Bool,
      polyEvalIdxOf nOut σ srcPool qm qlCur qhCur aCur 0 k +
      polyEvalIdxOf nOut σ srcPool qm ql qh aFinal i (n - i) =
      polyEval nOut σ srcPool qm ql qh n) (hka : k < aCur.length) :
    let ql' := qlCur.set h0.toNat l
    let qh' := qhCur.set h0.toNat h
    let a' := aCur.set k h0
    (∀ p < k + 1, ∃ idx < j, a'.getD p 0#32 = aFinal.getD idx 0#32) ∧
    (∀ t, j ≤ t → t < n → a'.getD t 0#32 = aFinal.getD t 0#32) ∧
    ((List.range (k + 1)).map (fun p => (a'.getD p 0#32).toNat)).Nodup ∧
    (∀ p < k + 1, (a'.getD p 0#32).toNat < n) ∧
    (∀ idx, (∀ p < k + 1, (a'.getD p 0#32).toNat ≠ idx) →
      ql'.getD idx 0#64 = ql.getD idx 0#64 ∧ qh'.getD idx 0#64 = qh.getD idx 0#64) ∧
    (∀ σ : Nat → Bool,
      polyEvalIdxOf nOut σ srcPool qm ql' qh' a' 0 (k + 1) +
        polyEvalIdxOf nOut σ srcPool qm ql qh aFinal j (n - j) =
        polyEval nOut σ srcPool qm ql qh n) := by
  intro ql' qh' a'
  have h0_lt : h0.toNat < n := by rw [hh0]; exact hpermF.mem_lt hi_lt
  have hh0_ql : h0.toNat < qlCur.length := by omega
  have hh0_qh : h0.toNat < qhCur.length := by omega
  have hnot_mem : ∀ p < k, (aCur.getD p 0#32).toNat ≠ h0.toNat := by
    intro p hp heqp
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := hsrc_a p hp
    have heqF : (aFinal.getD idx 0#32).toNat = (aFinal.getD i 0#32).toNat := by
      rw [← hidx_eq, heqp, hh0]
    have hc := nodup_getElem_inj hpermF.nodup (by simp; omega : idx < _) (by simp; omega : i < _)
      (by simpa [hidx_lt, hi_lt] using heqF)
    omega
  have hsrc' : ∀ p < k + 1, ∃ idx < j, a'.getD p 0#32 = aFinal.getD idx 0#32 := by
    intro p hp; dsimp only [a']; rw [getD_set_eq aCur 0#32 h0 hka]
    by_cases hpk : p = k
    · simp only [hpk, ↓reduceIte]; exact ⟨i, by omega, hh0⟩
    · simp only [hpk, ↓reduceIte]
      obtain ⟨idx, hidx, heq⟩ := hsrc_a p (by omega); exact ⟨idx, by omega, heq⟩
  have hrest' : ∀ t, j ≤ t → t < n → a'.getD t 0#32 = aFinal.getD t 0#32 := by
    intro t ht1 ht2; dsimp only [a']; rw [getD_set_eq aCur 0#32 h0 hka]
    simp only [show t ≠ k by omega, ↓reduceIte]; exact hrest_a t (by omega) ht2
  have hnd' : ((List.range (k + 1)).map (fun p => (a'.getD p 0#32).toNat)).Nodup := by
    rw [List.range_succ, List.map_append, List.map_singleton, List.nodup_append]
    have hcongr : (List.range k).map (fun p => (a'.getD p 0#32).toNat) =
        (List.range k).map (fun p => (aCur.getD p 0#32).toNat) := by
      apply List.map_congr_left; intro p hp
      have hpk := List.mem_range.mp hp
      dsimp only [a']; rw [getD_set_eq aCur 0#32 h0 hka]; simp [show p ≠ k by omega]
    refine ⟨by rwa [hcongr], by simp, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_singleton] at hy; subst hy; rw [hcongr] at hx
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
    dsimp only [a'] at hxy; rw [getD_set_eq aCur 0#32 h0 hka] at hxy; simp only [↓reduceIte] at hxy
    exact hnot_mem p (List.mem_range.mp hp) (by omega)
  have hlt' : ∀ p < k + 1, (a'.getD p 0#32).toNat < n := by
    intro p hp; dsimp only [a']; rw [getD_set_eq aCur 0#32 h0 hka]
    by_cases hpk : p = k
    · simp only [hpk, ↓reduceIte]; exact h0_lt
    · simp only [hpk, ↓reduceIte]; exact hlt_a p (by omega)
  have hql' : ∀ idx, (∀ p < k + 1, (a'.getD p 0#32).toNat ≠ idx) →
      ql'.getD idx 0#64 = ql.getD idx 0#64 ∧ qh'.getD idx 0#64 = qh.getD idx 0#64 := by
    intro idx hidx
    have hne_h0 : h0.toNat ≠ idx := by
      have hk1 := hidx k (Nat.lt_succ_self k)
      dsimp only [a'] at hk1; rw [getD_set_eq aCur 0#32 h0 hka] at hk1; simpa using hk1
    have hprev : ∀ p < k, (aCur.getD p 0#32).toNat ≠ idx := by
      intro p hp; have hp1 := hidx p (Nat.lt_succ_of_lt hp)
      dsimp only [a'] at hp1; rw [getD_set_eq aCur 0#32 h0 hka] at hp1
      simpa [show p ≠ k by omega] using hp1
    dsimp only [ql', qh']; rw [getD_set_eq qlCur 0#64 l hh0_ql, getD_set_eq qhCur 0#64 h hh0_qh]
    simp only [hne_h0.symm, ↓reduceIte]; exact hql_unmod idx hprev
  refine ⟨hsrc', hrest', hnd', hlt', hql', fun σ => ?_⟩
  have heval_k : polyEvalIdxOf nOut σ srcPool qm ql' qh' a' 0 k =
      polyEvalIdxOf nOut σ srcPool qm qlCur qhCur aCur 0 k := by
    apply polyEvalIdxOf_congr_coeff
    · intro t ht; dsimp only [a']
      rw [Nat.zero_add, getD_set_eq aCur 0#32 h0 hka]; simp [show t ≠ k by omega]
    · intro t ht; dsimp only [a', ql', qh']
      have hne := hnot_mem t ht
      have htk : t ≠ k := by omega
      rw [Nat.zero_add, getD_set_eq aCur 0#32 h0 hka]
      simp only [htk, ↓reduceIte]
      rw [getD_set_eq qlCur 0#64 l hh0_ql, getD_set_eq qhCur 0#64 h hh0_qh]
      simp only [hne, ↓reduceIte, and_self]
  have heval_kp1 : polyEvalIdxOf nOut σ srcPool qm ql' qh' a' 0 (k + 1) =
      polyEvalIdxOf nOut σ srcPool qm qlCur qhCur aCur 0 k +
        (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
         then coeff128 nOut l h else 0#nOut) := by
    rw [polyEvalIdxOf_succ, heval_k]; congr 1
    simp only [termEval, Nat.zero_add]; dsimp only [a', ql', qh']
    rw [getD_set_eq aCur 0#32 h0 hka, getD_set_eq qlCur 0#64 l hh0_ql,
      getD_set_eq qhCur 0#64 h hh0_qh]; simp
  rw [heval_kp1, BitVec.add_assoc, hsum σ, heval_old σ]

theorem CombineInv.step_emit {nOut : Nat}
    {srcPool qm : List (BitVec 32)} {ql qh qlC qhC : List (BitVec 64)}
    {aArr aC : List (BitVec 32)} {qn k i j : Nat} {h0 : BitVec 32} {l h : BitVec 64}
    {qlPtr qhPtr ixPtr : BitVec 64} {Rcmb : Mem 64 → Prop} {m' : Mem 64}
    (hqlC : qlC.length = ql.length) (hqhC : qhC.length = qh.length)
    (haC : aC.length = aArr.length) (hk_i : k ≤ i) (hi_lt : i < qn)
    (hj_lo : i + 1 ≤ j) (hj_qn : j ≤ qn) (hh0 : h0 = aArr.getD i 0#32)
    (hpermA : PermN aArr qn) (hqn_ql : qn ≤ ql.length) (hqn_qh : qn ≤ qh.length)
    (hka : k < aC.length)
    (hsrcA : ∀ p < k, ∃ idx < i, aC.getD p 0#32 = aArr.getD idx 0#32)
    (hrestA : ∀ t, i ≤ t → t < qn → aC.getD t 0#32 = aArr.getD t 0#32)
    (hndA : ((List.range k).map (fun p => (aC.getD p 0#32).toNat)).Nodup)
    (hltA : ∀ p < k, (aC.getD p 0#32).toNat < qn)
    (hqlU : ∀ idx, (∀ p < k, (aC.getD p 0#32).toNat ≠ idx) →
      qlC.getD idx 0#64 = ql.getD idx 0#64 ∧ qhC.getD idx 0#64 = qh.getD idx 0#64)
    (hsum : ∀ σ : Nat → Bool,
      (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr j (qn - j) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i (qn - i))
    (heval : ∀ σ : Nat → Bool,
      polyEvalIdxOf nOut σ srcPool qm qlC qhC aC 0 k +
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i (qn - i) =
      polyEval nOut σ srcPool qm ql qh qn)
    (hm' : (array64 qlPtr (qlC.set h0.toNat l) ⋆ array64 qhPtr (qhC.set h0.toNat h) ⋆
      array (t := i32) ixPtr (aC.set k h0) ⋆ Rcmb) m') :
    CombineInv nOut srcPool qm ql qh aArr qn qlPtr qhPtr ixPtr Rcmb (k + 1) j m' := by
  have ⟨hsrc', hrest', hnd', hlt', hql', heval'⟩ := combine_emit_ok hk_i hi_lt hj_lo hj_qn hh0
    hpermA hqlC hqhC hqn_ql hqn_qh hsrcA hrestA hndA hltA hqlU hsum heval hka
  exact ⟨qlC.set h0.toNat l, qhC.set h0.toNat h, aC.set k h0,
    by simp [hqlC], by simp [hqhC], by simp [haC], by omega, hj_qn,
    hsrc', hrest', hnd', hlt', hql', heval', hm'⟩

theorem CombineInv.hJ0_eval {nOut : Nat} {σ : Nat → Bool}
    {srcPool qm : List (BitVec 32)} {ql qh qlC qhC : List (BitVec 64)}
    {aArr : List (BitVec 32)} {qn i : Nat} {h0 : BitVec 32}
    (hh0_eq : h0 = aArr.getD i 0#32) (hsp : qn - i = (qn - (i + 1)) + 1)
    (hh0_ql : h0.toNat < qlC.length) (hh0_qh : h0.toNat < qhC.length)
    (hu : qlC.getD h0.toNat 0#64 = ql.getD h0.toNat 0#64 ∧
      qhC.getD h0.toNat 0#64 = qh.getD h0.toNat 0#64) :
    (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
      then coeff128 nOut (qlC[h0.toNat]'hh0_ql) (qhC[h0.toNat]'hh0_qh) else 0#nOut) +
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr (i + 1) (qn - (i + 1)) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i (qn - i) := by
  rw [← getD_eq_getElem qlC 0#64 hh0_ql, ← getD_eq_getElem qhC 0#64 hh0_qh,
    hsp, polyEvalIdxOf_split_one, hu.1, hu.2, hh0_eq]
  rfl

theorem CombineInv.step_skip {nOut : Nat}
    {srcPool qm : List (BitVec 32)} {ql qh qlC qhC : List (BitVec 64)}
    {aArr aC : List (BitVec 32)} {qn k i j : Nat} {h0 : BitVec 32} {l h : BitVec 64}
    {qlPtr qhPtr ixPtr : BitVec 64} {Rcmb : Mem 64 → Prop} {mC : Mem 64}
    (hqlC : qlC.length = ql.length) (hqhC : qhC.length = qh.length)
    (haC : aC.length = aArr.length) (hk_i : k ≤ i) (hj_lo : i + 1 ≤ j) (hj_qn : j ≤ qn)
    (hl0 : l = 0#64) (hh0' : h = 0#64)
    (hsrcA : ∀ p < k, ∃ idx < i, aC.getD p 0#32 = aArr.getD idx 0#32)
    (hrestA : ∀ t, i ≤ t → t < qn → aC.getD t 0#32 = aArr.getD t 0#32)
    (hndA : ((List.range k).map (fun p => (aC.getD p 0#32).toNat)).Nodup)
    (hltA : ∀ p < k, (aC.getD p 0#32).toNat < qn)
    (hqlU : ∀ idx, (∀ p < k, (aC.getD p 0#32).toNat ≠ idx) →
      qlC.getD idx 0#64 = ql.getD idx 0#64 ∧ qhC.getD idx 0#64 = qh.getD idx 0#64)
    (hsum : ∀ σ : Nat → Bool,
      (if monoValL σ (symListAt srcPool (qm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr j (qn - j) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i (qn - i))
    (heval : ∀ σ : Nat → Bool,
      polyEvalIdxOf nOut σ srcPool qm qlC qhC aC 0 k +
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i (qn - i) =
      polyEval nOut σ srcPool qm ql qh qn)
    (hmC : (array64 qlPtr qlC ⋆ array64 qhPtr qhC ⋆ array (t := i32) ixPtr aC ⋆ Rcmb) mC) :
    CombineInv nOut srcPool qm ql qh aArr qn qlPtr qhPtr ixPtr Rcmb k j mC := by
  have hjSum' : ∀ σ : Nat → Bool, polyEvalIdxOf nOut σ srcPool qm ql qh aArr j (qn - j) =
      polyEvalIdxOf nOut σ srcPool qm ql qh aArr i (qn - i) := fun σ => by
    simpa [hl0, hh0', coeff128] using hsum σ
  exact ⟨qlC, qhC, aC, hqlC, hqhC, haC, by omega, hj_qn,
    fun p hp => by obtain ⟨idx, hidx, heq⟩ := hsrcA p hp; exact ⟨idx, by omega, heq⟩,
    fun t ht1 ht2 => hrestA t (by omega) ht2, hndA, hltA, hqlU,
    fun σ => by rw [hjSum' σ]; exact heval σ, hmC⟩

end

end LeanQbe.T.Examples.Arisca.Proof

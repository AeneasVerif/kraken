/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly1Sort
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA Merge Products Helpers & Copy Phase (`Arisca.Proof.Poly1Merge`)

Pure range/word-sum invariants, focus lemma, `MergeProdInv` step lemmas, `Expr` matchers, and
the `while (curC < j)` copy-phase proof (`merge_products_copy_step`) for `ar_merge_products`.
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

/-! ## 1. Pure Helpers & Focus Lemma for `ar_merge_products` -/

section
public theorem strictIncBelow_cur_sub_bp {bx : List (BitVec 32)} {nb n bp cur : Nat}
    (hinc : strictIncBelow bx nb n) (hbp_le : bp ≤ nb) (hcur_n : cur ≤ n)
    (hlo : ∀ p < bp, (bx.getD p 0#32).toNat < cur)
    (hhi : bp < nb → cur ≤ (bx.getD bp 0#32).toNat) :
    bp ≤ cur ∧ cur - bp ≤ n - nb := by
  have h1 : bp ≤ cur := by
    cases bp with
    | zero => exact Nat.zero_le _
    | succ bp' =>
      have hinc_k : ∀ k, k ≤ bp' → k ≤ (bx.getD k 0#32).toNat := by
        intro k hk; induction k with
        | zero => exact Nat.zero_le _
        | succ k ih => have := ih (by omega); have := hinc.2 k (by omega); omega
      have := hlo bp' (Nat.lt_succ_self bp'); have := hinc_k bp' (le_refl _); omega
  have h2 : cur + (nb - bp) ≤ n := by
    by_cases hbp_lt : bp < nb
    · have hgap : ∀ d, bp + d < nb →
          (bx.getD bp 0#32).toNat + d ≤ (bx.getD (bp + d) 0#32).toNat := by
        intro d hd; induction d with
        | zero => simp
        | succ d ih =>
          have h1 := ih (by omega); have h2 := hinc.2 (bp + d) (by omega)
          rw [Nat.add_assoc] at h2; omega
      have hd := hgap (nb - 1 - bp) (by omega); have htop := hinc.1 (nb - 1) (by omega)
      have hbase := hhi hbp_lt; rw [show bp + (nb - 1 - bp) = nb - 1 by omega] at hd; omega
    · rw [show nb - bp = 0 by omega]; exact hcur_n
  exact ⟨h1, by omega⟩

public theorem tqMem_merge_focus (s : ArCtxState)
    (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
    (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
    (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2) :
    let srcPool := if s.pc.toNat = 0 then pool0 else pool1
    let srcTm := if s.tc.toNat = 0 then tm0 else tm1
    let srcTs := if s.tc.toNat = 0 then ts0 else ts1
    let srcTl := if s.tc.toNat = 0 then tl0 else tl1
    let srcTh := if s.tc.toNat = 0 then th0 else th1
    let dstTm0 := if s.tc.toNat = 0 then tm1 else tm0
    let dstTs0 := if s.tc.toNat = 0 then ts1 else ts0
    let dstTl0 := if s.tc.toNat = 0 then tl1 else tl0
    let dstTh0 := if s.tc.toNat = 0 then th1 else th0
    ∃ rest : Mem 64 → Prop,
      (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip =
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
         array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
         array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
         array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
         array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dstTm0 ⋆
         array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dstTs0 ⋆
         array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dstTl0 ⋆
         array64 (s.th.getD (1 - s.tc.toNat) 0#64) dstTh0 ⋆
         array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
         array (t := i32) s.ix ix ⋆ array (t := i32) s.bx bx ⋆ rest)) ∧
      (∀ (s' : ArCtxState) (dstTm : List (BitVec 32)) (dstTs dstTl dstTh : List (BitVec 64)),
        s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
        s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh →
        s'.ix = s.ix → s'.ix2 = s.ix2 → s'.bx = s.bx → s'.vq_off = s.vq_off →
        s'.vq = s.vq → s'.vq_skip = s.vq_skip →
        dstTm.length = dstTm0.length → dstTs.length = dstTs0.length →
        dstTl.length = dstTl0.length → dstTh.length = dstTh0.length →
        tMem s' (if s.tc.toNat = 0 then tm0 else dstTm) (if s.tc.toNat = 0 then dstTm else tm1)
            (if s.tc.toNat = 0 then ts0 else dstTs) (if s.tc.toNat = 0 then tl0 else dstTl)
            (if s.tc.toNat = 0 then th0 else dstTh) (if s.tc.toNat = 0 then dstTs else ts1)
            (if s.tc.toNat = 0 then dstTl else tl1) (if s.tc.toNat = 0 then dstTh else th1)
            pool0 pool1 ⋆ qMem s' qm qs ql qh ix ix2 bx vqOff vq vqSkip =
          (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
           array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
           array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆ array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
           array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
           array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dstTm ⋆
           array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dstTs ⋆
           array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dstTl ⋆
           array64 (s.th.getD (1 - s.tc.toNat) 0#64) dstTh ⋆
           array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
           array (t := i32) s.ix ix ⋆ array (t := i32) s.bx bx ⋆ rest)) := by
  have hpc' : s.pc = 0#32 ∨ s.pc = 1#32 := bv32_lt2_cases hpc
  have htc' : s.tc = 0#32 ∨ s.tc = 1#32 := bv32_lt2_cases htc
  have hu := arrayPad_u32_unfold
  rcases hpc' with h0 | h1 <;> rcases htc' with ht0 | ht1
  · refine ⟨arrayPad i32 (s.pool.getD 1 0#64) pool1 ⋆ u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆
      u32PadTail (s.tm.getD 0 0#64) tm0.length ⋆ u32PadTail (s.tm.getD 1 0#64) tm1.length ⋆
      u32PadTail s.qm qm.length ⋆ u32PadTail s.ix ix.length ⋆ arrayPad i32 s.ix2 ix2 ⋆
      u32PadTail s.bx bx.length ⋆ arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆
      arrayPad i8 s.vq_skip vqSkip,
      by simp only [tMem, qMem, h0, ht0, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          Nat.sub_zero, ↓reduceIte, hu]; ac_rfl,
      fun s' dTm dTs dTl dTh htm hts htl hth hpool hqm hqs hql hqh hix hix2 hbx hvqo hvq hvqs
        hdt1 _ _ _ => by
        simp only [tMem, qMem, h0, ht0, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          Nat.sub_zero, ↓reduceIte, hu, htm, hts, htl, hth, hpool, hqm, hqs, hql, hqh, hix, hix2,
          hbx, hvqo, hvq, hvqs, hdt1]; ac_rfl⟩
  · refine ⟨arrayPad i32 (s.pool.getD 1 0#64) pool1 ⋆ u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆
      u32PadTail (s.tm.getD 1 0#64) tm1.length ⋆ u32PadTail (s.tm.getD 0 0#64) tm0.length ⋆
      u32PadTail s.qm qm.length ⋆ u32PadTail s.ix ix.length ⋆ arrayPad i32 s.ix2 ix2 ⋆
      u32PadTail s.bx bx.length ⋆ arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆
      arrayPad i8 s.vq_skip vqSkip,
      by simp only [tMem, qMem, h0, ht1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          Nat.sub_self, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu]; ac_rfl,
      fun s' dTm dTs dTl dTh htm hts htl hth hpool hqm hqs hql hqh hix hix2 hbx hvqo hvq hvqs
        hdt1 _ _ _ => by
        simp only [tMem, qMem, h0, ht1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          Nat.sub_self, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu, htm, hts, htl, hth, hpool,
          hqm, hqs, hql, hqh, hix, hix2, hbx, hvqo, hvq, hvqs, hdt1]; ac_rfl⟩
  · refine ⟨arrayPad i32 (s.pool.getD 0 0#64) pool0 ⋆ u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆
      u32PadTail (s.tm.getD 0 0#64) tm0.length ⋆ u32PadTail (s.tm.getD 1 0#64) tm1.length ⋆
      u32PadTail s.qm qm.length ⋆ u32PadTail s.ix ix.length ⋆ arrayPad i32 s.ix2 ix2 ⋆
      u32PadTail s.bx bx.length ⋆ arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆
      arrayPad i8 s.vq_skip vqSkip,
      by simp only [tMem, qMem, h1, ht0, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          Nat.sub_zero, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu]; ac_rfl,
      fun s' dTm dTs dTl dTh htm hts htl hth hpool hqm hqs hql hqh hix hix2 hbx hvqo hvq hvqs
        hdt1 _ _ _ => by
        simp only [tMem, qMem, h1, ht0, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          Nat.sub_zero, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu, htm, hts, htl, hth, hpool,
          hqm, hqs, hql, hqh, hix, hix2, hbx, hvqo, hvq, hvqs, hdt1]; ac_rfl⟩
  · refine ⟨arrayPad i32 (s.pool.getD 0 0#64) pool0 ⋆ u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆
      u32PadTail (s.tm.getD 1 0#64) tm1.length ⋆ u32PadTail (s.tm.getD 0 0#64) tm0.length ⋆
      u32PadTail s.qm qm.length ⋆ u32PadTail s.ix ix.length ⋆ arrayPad i32 s.ix2 ix2 ⋆
      u32PadTail s.bx bx.length ⋆ arrayPad i32 s.vq_off vqOff ⋆ arrayPad i32 s.vq vq ⋆
      arrayPad i8 s.vq_skip vqSkip,
      by simp only [tMem, qMem, h1, ht1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          Nat.sub_self, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu]; ac_rfl,
      fun s' dTm dTs dTl dTh htm hts htl hth hpool hqm hqs hql hqh hix hix2 hbx hvqo hvq hvqs
        hdt1 _ _ _ => by
        simp only [tMem, qMem, h1, ht1, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
          Nat.sub_self, show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu, htm, hts, htl, hth, hpool,
          hqm, hqs, hql, hqh, hix, hix2, hbx, hvqo, hvq, hvqs, hdt1]; ac_rfl⟩

@[expose] public def tailWordSum (pool tm : List (BitVec 32)) (lo n : Nat) : Nat :=
  (List.range (n - lo)).foldl
    (fun acc d => acc + ((pool.getD (tm.getD (lo + d) 0#32).toNat 0#32).toNat + 1)) 0

@[expose] public def tailQWordSum (pool qm ix : List (BitVec 32)) (pi k : Nat) : Nat :=
  (List.range (k - pi)).foldl
    (fun acc d =>
      acc + ((pool.getD (qm.getD (ix.getD (pi + d) 0#32).toNat 0#32).toNat 0#32).toNat + 1)) 0

private theorem list_range_foldl_split (f : Nat → Nat) (a b : Nat) :
    (List.range (a + 1)).foldl (fun acc i => acc + f (b + i)) 0 =
      f b + (List.range a).foldl (fun acc i => acc + f (b + 1 + i)) 0 := by
  induction a with
  | zero => simp [List.range_succ, Nat.add_zero]
  | succ a ih =>
    rw [Nat.add_assoc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      show b + (a + 1) = b + 1 + a by omega]
    omega

private theorem list_range_foldl_congr {α : Type} (f g : Nat → α) (add : α → α → α)
    (init : α) (n : Nat) (h : ∀ i < n, f i = g i) :
    (List.range n).foldl (fun acc i => add acc (f i)) init =
      (List.range n).foldl (fun acc i => add acc (g i)) init := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

private theorem tailWordSum_split {pool tm : List (BitVec 32)} {lo n : Nat} (hlo : lo < n) :
    tailWordSum pool tm lo n =
      ((pool.getD (tm.getD lo 0#32).toNat 0#32).toNat + 1) + tailWordSum pool tm (lo + 1) n := by
  dsimp only [tailWordSum]; rw [show n - lo = (n - (lo + 1)) + 1 by omega]
  exact list_range_foldl_split
    (fun idx => (pool.getD (tm.getD idx 0#32).toNat 0#32).toNat + 1) (n - (lo + 1)) lo

private theorem tailQWordSum_split {pool qm ix : List (BitVec 32)} {pi k : Nat} (hpi : pi < k) :
    tailQWordSum pool qm ix pi k =
      ((pool.getD (qm.getD (ix.getD pi 0#32).toNat 0#32).toNat 0#32).toNat + 1) +
        tailQWordSum pool qm ix (pi + 1) k := by
  dsimp only [tailQWordSum]; rw [show k - pi = (k - (pi + 1)) + 1 by omega]
  exact list_range_foldl_split
    (fun idx => (pool.getD (qm.getD (ix.getD idx 0#32).toNat 0#32).toNat 0#32).toNat + 1)
    (k - (pi + 1)) pi

private theorem polyEval_set_eq {nOut : Nat} {σ : Nat → Bool}
    {pool dstTm : List (BitVec 32)} {dstTl dstTh : List (BitVec 64)}
    {o : Nat} (ho : o < dstTm.length) (hol : o < dstTl.length) (hoh : o < dstTh.length)
    (mOff : BitVec 32) (l h : BitVec 64) :
    polyEval nOut σ pool (dstTm.set o mOff) (dstTl.set o l) (dstTh.set o h) (o + 1) =
      polyEval nOut σ pool dstTm dstTl dstTh o +
        (if monoValL σ (symListAt pool mOff.toNat) then coeff128 nOut l h else 0#nOut) := by
  rw [polyEval, polyEvalRange_succ]
  have heq : polyEvalRange nOut σ pool (dstTm.set o mOff) (dstTl.set o l) (dstTh.set o h) 0 o =
      polyEval nOut σ pool dstTm dstTl dstTh o := by
    dsimp only [polyEval, polyEvalRange]
    refine list_range_foldl_congr _ _ (· + ·) 0#nOut o (fun t ht => ?_)
    simp only [termEval, Nat.zero_add]
    rw [getD_set_eq dstTm 0#32 mOff ho, getD_set_eq dstTl 0#64 l hol,
      getD_set_eq dstTh 0#64 h hoh]
    simp [show t ≠ o by omega]
  rw [heq]; congr 1
  simp only [termEval, Nat.zero_add, getD_set_eq dstTm 0#32 mOff ho,
    getD_set_eq dstTl 0#64 l hol, getD_set_eq dstTh 0#64 h hoh, ↓reduceIte]

private theorem nonBxRangeSum_copy_step {nOut : Nat} {σ : Nat → Bool}
    {srcPool srcTm bx : List (BitVec 32)} {srcTl srcTh : List (BitVec 64)}
    {nb n cur bp : Nat}
    (hinc : strictIncBelow bx nb n) (hnb : nb ≤ bx.length) (hbp_le : bp ≤ nb)
    (hlo : ∀ p < bp, (bx.getD p 0#32).toNat < cur)
    (hhi : bp < nb → cur ≤ (bx.getD bp 0#32).toNat)
    (hne : ¬ (bp < nb ∧ (bx.getD bp 0#32).toNat = cur)) :
    nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 (cur + 1) =
      nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 cur +
        termEval nOut σ srcPool srcTm srcTl srcTh cur := by
  rw [nonBxRangeSum_succ, Nat.zero_add, strictIncBelow.any_eq hinc hnb hbp_le hlo hhi]
  by_cases hbp : bp < nb
  · have hne' : (bx.getD bp 0#32).toNat ≠ cur := fun h => hne ⟨hbp, h⟩
    rw [beq_false_of_ne hne']; simp [hbp]
  · simp [hbp]

private theorem nonBxRangeSum_skip_bx {nOut : Nat} {σ : Nat → Bool}
    {srcPool srcTm bx : List (BitVec 32)} {srcTl srcTh : List (BitVec 64)}
    {nb n e bp : Nat}
    (hinc : strictIncBelow bx nb n) (hnb : nb ≤ bx.length) (hbp_lt : bp < nb)
    (hlo : ∀ p < bp, (bx.getD p 0#32).toNat < e) (heq : (bx.getD bp 0#32).toNat = e) :
    nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 (e + 1) =
      nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 e := by
  have hany : (bx.take nb).any (fun x => x.toNat == e) = true := by
    rw [strictIncBelow.any_eq hinc hnb (le_of_lt hbp_lt) hlo (fun _ => le_of_eq heq.symm)]
    rw [beq_iff_eq.mpr heq]; simp [hbp_lt]
  rw [nonBxRangeSum_succ, Nat.zero_add, hany]; simp

private theorem merge_cadd_eval_step {nOut : Nat} {σ : Nat → Bool}
    {srcPool srcTm qm bx ixS dTm : List (BitVec 32)}
    {srcTl srcTh qlS qhS dTl dTh : List (BitVec 64)}
    {nl nh : BitVec 64} {nb n bp pi o j : Nat}
    (hsym : symListAt srcPool (srcTm.getD j 0#32).toNat =
      symListAt srcPool (qm.getD (ixS.getD pi 0#32).toNat 0#32).toNat)
    (ho : o < dTm.length) (hol : o < dTl.length) (hoh : o < dTh.length)
    (hinc : strictIncBelow bx nb n) (hnb : nb ≤ bx.length) (hbp_le : bp ≤ nb)
    (hlo : ∀ p < bp, (bx.getD p 0#32).toNat < j)
    (hhi : bp < nb → j ≤ (bx.getD bp 0#32).toNat)
    (hne : ¬ (bp < nb ∧ (bx.getD bp 0#32).toNat = j))
    (hcadd : coeff128 nOut nl nh = coeff128 nOut (srcTl.getD j 0#64) (srcTh.getD j 0#64) +
      coeff128 nOut (qlS.getD (ixS.getD pi 0#32).toNat 0#64)
        (qhS.getD (ixS.getD pi 0#32).toNat 0#64))
    (hcur : polyEval nOut σ srcPool dTm dTl dTh o =
      nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 j +
        polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 pi) :
    (if nl ≠ 0#64 ∨ nh ≠ 0#64 then
      polyEval nOut σ srcPool (dTm.set o (srcTm.getD j 0#32)) (dTl.set o nl) (dTh.set o nh) (o + 1)
     else polyEval nOut σ srcPool dTm dTl dTh o) =
      nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 (j + 1) +
        polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 (pi + 1) := by
  rw [nonBxRangeSum_copy_step hinc hnb hbp_le hlo hhi hne, polyEvalIdxOf_succ, Nat.zero_add]
  have hterm : termEval nOut σ srcPool srcTm srcTl srcTh j +
      termEval nOut σ srcPool qm qlS qhS (ixS.getD pi 0#32).toNat =
      if monoValL σ (symListAt srcPool (srcTm.getD j 0#32).toNat) then coeff128 nOut nl nh
      else 0#nOut := by
    simp only [termEval, ← hsym]
    cases monoValL σ (symListAt srcPool (srcTm.getD j 0#32).toNat)
    · simp
    · simp [hcadd]
  have hrhs : nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 j +
      termEval nOut σ srcPool srcTm srcTl srcTh j +
      (polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 pi +
        termEval nOut σ srcPool qm qlS qhS (ixS.getD pi 0#32).toNat) =
      polyEval nOut σ srcPool dTm dTl dTh o +
        (if monoValL σ (symListAt srcPool (srcTm.getD j 0#32).toNat) then coeff128 nOut nl nh
         else 0#nOut) := by
    rw [← hterm, hcur]; ac_rfl
  rw [hrhs]
  by_cases hnz : nl ≠ 0#64 ∨ nh ≠ 0#64
  · simp only [hnz, ↓reduceIte, polyEval_set_eq ho hol hoh]
  · have hl0 : nl = 0#64 := Classical.byContradiction (fun h => hnz (Or.inl h))
    have hh0 : nh = 0#64 := Classical.byContradiction (fun h => hnz (Or.inr h))
    simp only [hnz]; simp [hl0, hh0, coeff128]

public theorem tailWordSum_zero (pool tm : List (BitVec 32)) (n : Nat) :
    tailWordSum pool tm 0 n = monoTotalWords pool tm n := by
  simp [tailWordSum, monoTotalWords]

public theorem tailWordSum_nil (pool tm : List (BitVec 32)) (n : Nat) :
    tailWordSum pool tm n n = 0 := by
  simp [tailWordSum]

public theorem tailQWordSum_nil (pool qm ix : List (BitVec 32)) (k : Nat) :
    tailQWordSum pool qm ix k k = 0 := by
  simp [tailQWordSum]

public theorem tailQWordSum_zero_le {pool qm ix : List (BitVec 32)} {k qn : Nat}
    (hnd : ((List.range k).map (fun p => (ix.getD p 0#32).toNat)).Nodup)
    (hlt : ∀ p < k, (ix.getD p 0#32).toNat < qn) :
    tailQWordSum pool qm ix 0 k ≤ monoTotalWords pool qm qn := by
  simpa [tailQWordSum] using monoTotalWords_le_of_nodup hnd hlt

private theorem monoTotalWords_set_eq {pool dstTm : List (BitVec 32)} {o : Nat}
    (ho : o < dstTm.length) (mOff : BitVec 32) :
    monoTotalWords pool (dstTm.set o mOff) (o + 1) =
      monoTotalWords pool dstTm o + ((pool.getD mOff.toNat 0#32).toNat + 1) := by
  dsimp only [monoTotalWords]
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have heq : (List.range o).foldl (fun acc i =>
      acc + ((pool.getD ((dstTm.set o mOff).getD i 0#32).toNat 0#32).toNat + 1)) 0 =
      (List.range o).foldl (fun acc i =>
        acc + ((pool.getD (dstTm.getD i 0#32).toNat 0#32).toNat + 1)) 0 := by
    refine list_range_foldl_congr _ _ (· + ·) 0 o (fun t ht => ?_)
    rw [getD_set_eq dstTm 0#32 mOff ho]; simp [show t ≠ o by omega]
  rw [heq, getD_set_eq dstTm 0#32 mOff ho]; simp

public theorem merge_bx_all_visited {bx : List (BitVec 32)} {nb n bp : Nat}
    (hinc : strictIncBelow bx nb n) (hbp_le : bp ≤ nb)
    (hhi : bp < nb → n ≤ (bx.getD bp 0#32).toNat) : bp = nb := by
  by_cases hbp : bp < nb
  · have h1 := hhi hbp; have h2 := hinc.1 bp hbp; omega
  · omega

@[expose] public def MergeProdInv (_n tn qn nb k nOut ptop : Nat)
    (srcPool srcTm qm ixS bx : List (BitVec 32)) (srcTl srcTh qlS qhS : List (BitVec 64))
    (dTmPtr dTsPtr dTlPtr dThPtr : BitVec 64) (dTmLen dTsLen dTlLen dThLen : Nat)
    (Rro : Mem 64 → Prop) (pi cur bp o : Nat) (mL : Mem 64) : Prop :=
  ∃ (dTm : List (BitVec 32)) (dTs dTl dTh : List (BitVec 64)),
    dTm.length = dTmLen ∧ dTs.length = dTsLen ∧ dTl.length = dTlLen ∧ dTh.length = dThLen ∧
    pi ≤ k ∧ bp ≤ nb ∧ cur ≤ tn ∧ o ≤ cur - bp + pi ∧
    (∀ p < bp, (bx.getD p 0#32).toNat < cur) ∧
    (bp < nb → cur ≤ (bx.getD bp 0#32).toNat) ∧
    (∀ t < o, MonoSliceOk srcPool (dTm.getD t 0#32).toNat ptop ∧
      (srcPool.getD (dTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    (∀ t < o, MonoSorted srcPool (dTm.getD t 0#32).toNat) ∧
    SigOk srcPool dTm dTs o ∧
    monoTotalWords srcPool dTm o + tailWordSum srcPool srcTm cur tn +
        tailQWordSum srcPool qm ixS pi k ≤
      monoTotalWords srcPool srcTm tn + tailQWordSum srcPool qm ixS 0 k ∧
    (∀ t < o, (∃ idx < tn, dTm.getD t 0#32 = srcTm.getD idx 0#32) ∨
      (∃ qidx < qn, dTm.getD t 0#32 = qm.getD qidx 0#32)) ∧
    (∀ σ : Nat → Bool,
      polyEval nOut σ srcPool dTm dTl dTh o =
        nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 cur +
          polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 pi) ∧
    (array (t := i32) dTmPtr dTm ⋆ array64 dTsPtr dTs ⋆
      array64 dTlPtr dTl ⋆ array64 dThPtr dTh ⋆ Rro) mL

private theorem merge_copy_step {n tn qn nb k nOut ptop pi cur bp o : Nat}
    {srcPool srcTm qm ixS bx dTm : List (BitVec 32)}
    {srcTs srcTl srcTh qlS qhS dTs dTl dTh : List (BitVec 64)}
    {dTmPtr dTsPtr dTlPtr dThPtr : BitVec 64} {dTmLen dTsLen dTlLen dThLen : Nat}
    {Rro : Mem 64 → Prop} {m' : Mem 64}
    (hinc : strictIncBelow bx nb tn) (hnb : nb ≤ bx.length)
    (hTmOk : ∀ t < tn, MonoSliceOk srcPool (srcTm.getD t 0#32).toNat ptop ∧
      (srcPool.getD (srcTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hTmSorted : ∀ t < tn, MonoSorted srcPool (srcTm.getD t 0#32).toNat)
    (hTmSig : SigOk srcPool srcTm srcTs tn)
    (hdTm : dTm.length = dTmLen) (hdTs : dTs.length = dTsLen)
    (hdTl : dTl.length = dTlLen) (hdTh : dTh.length = dThLen)
    (hpi : pi ≤ k) (hbp : bp ≤ nb) (hcur1 : cur + 1 ≤ tn)
    (ho_le : o ≤ cur - bp + pi) (ho_len : o < dTm.length)
    (hlo : ∀ p < bp, (bx.getD p 0#32).toNat < cur)
    (hhi : bp < nb → cur + 1 ≤ (bx.getD bp 0#32).toNat)
    (hOk : ∀ t < o, MonoSliceOk srcPool (dTm.getD t 0#32).toNat ptop ∧
      (srcPool.getD (dTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ t < o, MonoSorted srcPool (dTm.getD t 0#32).toNat)
    (hSig : SigOk srcPool dTm dTs o)
    (hwords : monoTotalWords srcPool dTm o + tailWordSum srcPool srcTm cur tn +
      tailQWordSum srcPool qm ixS pi k ≤
      monoTotalWords srcPool srcTm tn + tailQWordSum srcPool qm ixS 0 k)
    (hSrcT : ∀ t < o, (∃ idx < tn, dTm.getD t 0#32 = srcTm.getD idx 0#32) ∨
      (∃ qidx < qn, dTm.getD t 0#32 = qm.getD qidx 0#32))
    (heval : ∀ σ : Nat → Bool,
      polyEval nOut σ srcPool dTm dTl dTh o =
        nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 cur +
          polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 pi)
    {nv_m : BitVec 32} {nv_s nv_l nv_h : BitVec 64}
    (hvm : nv_m = srcTm.getD cur 0#32) (hvs : nv_s = srcTs.getD cur 0#64)
    (hvl : nv_l = srcTl.getD cur 0#64) (hvh : nv_h = srcTh.getD cur 0#64)
    (hos : o < dTs.length) (hol : o < dTl.length) (hoh : o < dTh.length)
    (hm' : (array (t := i32) dTmPtr (dTm.set o nv_m) ⋆ array64 dTsPtr (dTs.set o nv_s) ⋆
      array64 dTlPtr (dTl.set o nv_l) ⋆ array64 dThPtr (dTh.set o nv_h) ⋆ Rro) m') :
    MergeProdInv n tn qn nb k nOut ptop srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
      dTmPtr dTsPtr dTlPtr dThPtr dTmLen dTsLen dTlLen dThLen Rro
      pi (cur + 1) bp (o + 1) m' := by
  have hcur_lt : cur < tn := by omega
  have hne : ¬(bp < nb ∧ (bx.getD bp 0#32).toNat = cur) := fun ⟨h1, h2⟩ => by
    have := hhi h1; omega
  have hlo' : ∀ p < bp, (bx.getD p 0#32).toNat < cur + 1 := fun p hp =>
    Nat.lt_trans (hlo p hp) (Nat.lt_succ_self _)
  have hbp_le_cur : bp ≤ cur := (strictIncBelow_cur_sub_bp hinc hbp (by omega) hlo
    (fun h => Nat.le_of_lt (by have := hhi h; omega))).1
  have hOk' : ∀ t < o + 1, MonoSliceOk srcPool ((dTm.set o nv_m).getD t 0#32).toNat ptop ∧
      (srcPool.getD ((dTm.set o nv_m).getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 := by
    intro t ht; rw [getD_set_eq dTm 0#32 nv_m ho_len]
    by_cases hto : t = o
    · simp only [hto, ↓reduceIte, hvm]; exact hTmOk cur hcur_lt
    · simp only [hto, ↓reduceIte]; exact hOk t (by omega)
  have hSorted' : ∀ t < o + 1, MonoSorted srcPool ((dTm.set o nv_m).getD t 0#32).toNat := by
    intro t ht; rw [getD_set_eq dTm 0#32 nv_m ho_len]
    by_cases hto : t = o
    · simp only [hto, ↓reduceIte, hvm]; exact hTmSorted cur hcur_lt
    · simp only [hto, ↓reduceIte]; exact hSorted t (by omega)
  have hSig' : SigOk srcPool (dTm.set o nv_m) (dTs.set o nv_s) (o + 1) := by
    intro t ht x hx
    rw [getD_set_eq dTm 0#32 nv_m ho_len] at hx
    rw [getD_set_eq dTs 0#64 nv_s hos]
    by_cases hto : t = o
    · simp only [hto, ↓reduceIte, hvm, hvs] at hx ⊢; exact hTmSig cur hcur_lt x hx
    · simp only [hto, ↓reduceIte] at hx ⊢; exact hSig t (by omega) x hx
  have hwords' : monoTotalWords srcPool (dTm.set o nv_m) (o + 1) +
      tailWordSum srcPool srcTm (cur + 1) tn + tailQWordSum srcPool qm ixS pi k ≤
      monoTotalWords srcPool srcTm tn + tailQWordSum srcPool qm ixS 0 k := by
    rw [monoTotalWords_set_eq ho_len nv_m, hvm]
    rw [tailWordSum_split hcur_lt] at hwords; omega
  have hSrcT' : ∀ t < o + 1,
      (∃ idx < tn, (dTm.set o nv_m).getD t 0#32 = srcTm.getD idx 0#32) ∨
      (∃ qidx < qn, (dTm.set o nv_m).getD t 0#32 = qm.getD qidx 0#32) := by
    intro t ht; rw [getD_set_eq dTm 0#32 nv_m ho_len]
    by_cases hto : t = o
    · simp only [hto, ↓reduceIte, hvm]; exact Or.inl ⟨cur, hcur_lt, rfl⟩
    · simp only [hto, ↓reduceIte]; exact hSrcT t (by omega)
  have heval' : ∀ σ : Nat → Bool,
      polyEval nOut σ srcPool (dTm.set o nv_m) (dTl.set o nv_l) (dTh.set o nv_h) (o + 1) =
        nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 (cur + 1) +
          polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 pi := fun σ => by
    rw [polyEval_set_eq ho_len hol hoh, nonBxRangeSum_copy_step hinc hnb hbp hlo
      (fun h => Nat.le_of_lt (by have := hhi h; omega)) hne, hvm, hvl, hvh, heval σ]
    simp only [termEval]; ac_rfl
  exact ⟨dTm.set o nv_m, dTs.set o nv_s, dTl.set o nv_l, dTh.set o nv_h,
    by simp [hdTm], by simp [hdTs], by simp [hdTl], by simp [hdTh],
    hpi, hbp, hcur1, by omega, hlo', hhi, hOk', hSorted', hSig', hwords', hSrcT', heval', hm'⟩

private theorem merge_skip_bx_step {n tn qn nb k nOut ptop pi e j bp o : Nat}
    {srcPool srcTm qm ixS bx : List (BitVec 32)} {srcTl srcTh qlS qhS : List (BitVec 64)}
    {dTmPtr dTsPtr dTlPtr dThPtr : BitVec 64} {dTmLen dTsLen dTlLen dThLen : Nat}
    {Rro : Mem 64 → Prop} {m' : Mem 64}
    (hinc : strictIncBelow bx nb tn) (hnb : nb ≤ bx.length) (hj_tn : j ≤ tn)
    (he_j : e ≤ j)
    (hinv : MergeProdInv n tn qn nb k nOut ptop srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
      dTmPtr dTsPtr dTlPtr dThPtr dTmLen dTsLen dTlLen dThLen Rro pi e bp o m')
    (hlt_arm : e < j → bp < nb ∧ (bx.getD bp 0#32).toNat = e) :
    let cur' := if e < j then e + 1 else j
    let bp' := if e < j then bp + 1 else bp
    MergeProdInv n tn qn nb k nOut ptop srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
      dTmPtr dTsPtr dTlPtr dThPtr dTmLen dTsLen dTlLen dThLen Rro pi cur' bp' o m' := by
  obtain ⟨dTm, dTs, dTl, dTh, h1, h2, h3, h4, hpi, hbp, he_tn, ho_le, hlo, hhi,
    hOk, hSorted, hSig, hwords, hSrcT, heval, hm'⟩ := hinv
  by_cases hej : e < j
  · simp only [hej, ↓reduceIte]
    obtain ⟨hbp_lt, hbx_eq⟩ := hlt_arm hej
    have hlo' : ∀ p < bp + 1, (bx.getD p 0#32).toNat < e + 1 := by
      intro p hp
      by_cases hpbp : p = bp
      · rw [hpbp, hbx_eq]; exact Nat.lt_succ_self _
      · exact Nat.lt_trans (hlo p (by omega)) (Nat.lt_succ_self _)
    have hhi' : bp + 1 < nb → e + 1 ≤ (bx.getD (bp + 1) 0#32).toNat := by
      intro hlt; have := hinc.2 bp hlt; omega
    have hbp_le_e : bp ≤ e := (strictIncBelow_cur_sub_bp hinc hbp he_tn hlo hhi).1
    have hskip : ∀ σ : Nat → Bool,
        nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 (e + 1) =
          nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 e := fun σ =>
      nonBxRangeSum_skip_bx (nOut := nOut) (σ := σ) (srcPool := srcPool)
        (srcTm := srcTm) (srcTl := srcTl) (srcTh := srcTh) hinc hnb hbp_lt hlo hbx_eq
    have hwords' : monoTotalWords srcPool dTm o + tailWordSum srcPool srcTm (e + 1) tn +
        tailQWordSum srcPool qm ixS pi k ≤
        monoTotalWords srcPool srcTm tn + tailQWordSum srcPool qm ixS 0 k := by
      rw [tailWordSum_split (by omega : e < tn)] at hwords; omega
    exact ⟨dTm, dTs, dTl, dTh, h1, h2, h3, h4, hpi, by omega, by omega, by omega,
      hlo', hhi', hOk, hSorted, hSig, hwords', hSrcT, fun σ => by rw [hskip σ]; exact heval σ, hm'⟩
  · have heeq : e = j := by omega
    subst heeq; simp only [Nat.lt_irrefl, ↓reduceIte]
    exact ⟨dTm, dTs, dTl, dTh, h1, h2, h3, h4, hpi, hbp, he_tn, ho_le, hlo, hhi,
      hOk, hSorted, hSig, hwords, hSrcT, heval, hm'⟩

public theorem merge_cadd_step {n tn qn nb k nOut ptop pi j bp o : Nat}
    {srcPool srcTm qm ixS bx dTm : List (BitVec 32)}
    {srcTs srcTl srcTh qlS qhS dTs dTl dTh : List (BitVec 64)}
    {dTmPtr dTsPtr dTlPtr dThPtr : BitVec 64} {dTmLen dTsLen dTlLen dThLen : Nat}
    {Rro : Mem 64 → Prop} {nl nh : BitVec 64} {ns : BitVec 64} {m' : Mem 64}
    (hinc : strictIncBelow bx nb tn) (hnb : nb ≤ bx.length)
    (hTmOk : ∀ t < tn, MonoSliceOk srcPool (srcTm.getD t 0#32).toNat ptop ∧
      (srcPool.getD (srcTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hTmSorted : ∀ t < tn, MonoSorted srcPool (srcTm.getD t 0#32).toNat)
    (hTmSig : SigOk srcPool srcTm srcTs tn)
    (hsym : symListAt srcPool (srcTm.getD j 0#32).toNat =
      symListAt srcPool (qm.getD (ixS.getD pi 0#32).toNat 0#32).toNat)
    (hcadd : coeff128 nOut nl nh = coeff128 nOut (srcTl.getD j 0#64) (srcTh.getD j 0#64) +
      coeff128 nOut (qlS.getD (ixS.getD pi 0#32).toNat 0#64)
        (qhS.getD (ixS.getD pi 0#32).toNat 0#64))
    (hne : ¬(bp < nb ∧ (bx.getD bp 0#32).toNat = j))
    (hdTm : dTm.length = dTmLen) (hdTs : dTs.length = dTsLen)
    (hdTl : dTl.length = dTlLen) (hdTh : dTh.length = dThLen)
    (hpi : pi < k) (hbp : bp ≤ nb) (hj_lt : j < tn)
    (ho_le : o ≤ j - bp + pi) (ho_len : o < dTm.length)
    (hos : o < dTs.length) (hol : o < dTl.length) (hoh : o < dTh.length)
    (hns : ns = srcTs.getD j 0#64)
    (hlo : ∀ p < bp, (bx.getD p 0#32).toNat < j)
    (hhi : bp < nb → j ≤ (bx.getD bp 0#32).toNat)
    (hOk : ∀ t < o, MonoSliceOk srcPool (dTm.getD t 0#32).toNat ptop ∧
      (srcPool.getD (dTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ t < o, MonoSorted srcPool (dTm.getD t 0#32).toNat)
    (hSig : SigOk srcPool dTm dTs o)
    (hwords : monoTotalWords srcPool dTm o + tailWordSum srcPool srcTm j tn +
      tailQWordSum srcPool qm ixS pi k ≤
      monoTotalWords srcPool srcTm tn + tailQWordSum srcPool qm ixS 0 k)
    (hSrcT : ∀ t < o, (∃ idx < tn, dTm.getD t 0#32 = srcTm.getD idx 0#32) ∨
      (∃ qidx < qn, dTm.getD t 0#32 = qm.getD qidx 0#32))
    (heval : ∀ σ : Nat → Bool,
      polyEval nOut σ srcPool dTm dTl dTh o =
        nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 j +
          polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 pi)
    (hm' : (if nl ≠ 0#64 ∨ nh ≠ 0#64 then
      array (t := i32) dTmPtr (dTm.set o (srcTm.getD j 0#32)) ⋆
        array64 dTsPtr (dTs.set o ns) ⋆ array64 dTlPtr (dTl.set o nl) ⋆
        array64 dThPtr (dTh.set o nh) ⋆ Rro
      else array (t := i32) dTmPtr dTm ⋆ array64 dTsPtr dTs ⋆
        array64 dTlPtr dTl ⋆ array64 dThPtr dTh ⋆ Rro) m') :
    let o' := if nl ≠ 0#64 ∨ nh ≠ 0#64 then o + 1 else o
    MergeProdInv n tn qn nb k nOut ptop srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
      dTmPtr dTsPtr dTlPtr dThPtr dTmLen dTsLen dTlLen dThLen Rro
      (pi + 1) (j + 1) bp o' m' := by
  have hbp_le_j : bp ≤ j := (strictIncBelow_cur_sub_bp hinc hbp (by omega) hlo hhi).1
  have hlo' : ∀ p < bp, (bx.getD p 0#32).toNat < j + 1 := fun p hp =>
    Nat.lt_trans (hlo p hp) (Nat.lt_succ_self _)
  have hhi' : bp < nb → j + 1 ≤ (bx.getD bp 0#32).toNat := fun h => by
    have h1 := hhi h; have h2 : (bx.getD bp 0#32).toNat ≠ j := fun he => hne ⟨h, he⟩; omega
  have heval' : ∀ σ : Nat → Bool,
      (if nl ≠ 0#64 ∨ nh ≠ 0#64 then
        polyEval nOut σ srcPool (dTm.set o (srcTm.getD j 0#32))
          (dTl.set o nl) (dTh.set o nh) (o + 1)
       else polyEval nOut σ srcPool dTm dTl dTh o) =
        nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 (j + 1) +
          polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 (pi + 1) := fun σ =>
    merge_cadd_eval_step hsym ho_len hol hoh hinc hnb hbp hlo hhi hne hcadd (heval σ)
  rw [tailWordSum_split hj_lt, tailQWordSum_split hpi] at hwords
  by_cases hnz : nl ≠ 0#64 ∨ nh ≠ 0#64
  · simp only [hnz, ↓reduceIte] at hm' heval' ⊢
    refine ⟨dTm.set o (srcTm.getD j 0#32), dTs.set o ns, dTl.set o nl, dTh.set o nh,
      by simp [hdTm], by simp [hdTs], by simp [hdTl], by simp [hdTh],
      by omega, hbp, by omega, by omega, hlo', hhi', ?_, ?_, ?_, ?_, ?_, heval', hm'⟩
    · intro t ht; rw [getD_set_eq dTm 0#32 _ ho_len]
      by_cases hto : t = o
      · simp only [hto, ↓reduceIte]; exact hTmOk j hj_lt
      · simp only [hto, ↓reduceIte]; exact hOk t (by omega)
    · intro t ht; rw [getD_set_eq dTm 0#32 _ ho_len]
      by_cases hto : t = o
      · simp only [hto, ↓reduceIte]; exact hTmSorted j hj_lt
      · simp only [hto, ↓reduceIte]; exact hSorted t (by omega)
    · intro t ht x hx
      rw [getD_set_eq dTm 0#32 _ ho_len] at hx
      rw [getD_set_eq dTs 0#64 _ hos]
      by_cases hto : t = o
      · simp only [hto, ↓reduceIte, hns] at hx ⊢; exact hTmSig j hj_lt x hx
      · simp only [hto, ↓reduceIte] at hx ⊢; exact hSig t (by omega) x hx
    · rw [monoTotalWords_set_eq ho_len]; omega
    · intro t ht; rw [getD_set_eq dTm 0#32 _ ho_len]
      by_cases hto : t = o
      · simp only [hto, ↓reduceIte]; exact Or.inl ⟨j, hj_lt, rfl⟩
      · simp only [hto, ↓reduceIte]; exact hSrcT t (by omega)
  · simp only [hnz, ↓reduceIte] at hm' heval' ⊢
    exact ⟨dTm, dTs, dTl, dTh, hdTm, hdTs, hdTl, hdTh, by omega, hbp, by omega, by omega,
      hlo', hhi', hOk, hSorted, hSig, by omega, hSrcT, heval', hm'⟩

public theorem merge_push_q_step {n tn qn nb k nOut ptop pi j bp o : Nat}
    {srcPool srcTm qm ixS bx dTm : List (BitVec 32)}
    {qs srcTl srcTh qlS qhS dTs dTl dTh : List (BitVec 64)}
    {dTmPtr dTsPtr dTlPtr dThPtr : BitVec 64} {dTmLen dTsLen dTlLen dThLen : Nat}
    {Rro : Mem 64 → Prop} {a : BitVec 32} {qs_a ql_a qh_a : BitVec 64} {m' : Mem 64}
    (hQmOk : ∀ t < qn, MonoSliceOk srcPool (qm.getD t 0#32).toNat ptop ∧
      (srcPool.getD (qm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hQmSorted : ∀ t < qn, MonoSorted srcPool (qm.getD t 0#32).toNat)
    (hQmSig : SigOk srcPool qm qs qn)
    (ha_eq : a = ixS.getD pi 0#32) (ha_lt : a.toNat < qn)
    (hqs_eq : qs_a = qs.getD a.toNat 0#64)
    (hql_eq : ql_a = qlS.getD a.toNat 0#64) (hqh_eq : qh_a = qhS.getD a.toNat 0#64)
    (hdTm : dTm.length = dTmLen) (hdTs : dTs.length = dTsLen)
    (hdTl : dTl.length = dTlLen) (hdTh : dTh.length = dThLen)
    (hpi : pi < k) (hbp : bp ≤ nb) (hj_tn : j ≤ tn)
    (ho_le : o ≤ j - bp + pi) (ho_len : o < dTm.length)
    (hos : o < dTs.length) (hol : o < dTl.length) (hoh : o < dTh.length)
    (hlo : ∀ p < bp, (bx.getD p 0#32).toNat < j)
    (hhi : bp < nb → j ≤ (bx.getD bp 0#32).toNat)
    (hOk : ∀ t < o, MonoSliceOk srcPool (dTm.getD t 0#32).toNat ptop ∧
      (srcPool.getD (dTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted : ∀ t < o, MonoSorted srcPool (dTm.getD t 0#32).toNat)
    (hSig : SigOk srcPool dTm dTs o)
    (hwords : monoTotalWords srcPool dTm o + tailWordSum srcPool srcTm j tn +
      tailQWordSum srcPool qm ixS pi k ≤
      monoTotalWords srcPool srcTm tn + tailQWordSum srcPool qm ixS 0 k)
    (hSrcT : ∀ t < o, (∃ idx < tn, dTm.getD t 0#32 = srcTm.getD idx 0#32) ∨
      (∃ qidx < qn, dTm.getD t 0#32 = qm.getD qidx 0#32))
    (heval : ∀ σ : Nat → Bool,
      polyEval nOut σ srcPool dTm dTl dTh o =
        nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 j +
          polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 pi)
    (hm' : (array (t := i32) dTmPtr (dTm.set o (qm.getD a.toNat 0#32)) ⋆
      array64 dTsPtr (dTs.set o qs_a) ⋆ array64 dTlPtr (dTl.set o ql_a) ⋆
      array64 dThPtr (dTh.set o qh_a) ⋆ Rro) m') :
    MergeProdInv n tn qn nb k nOut ptop srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
      dTmPtr dTsPtr dTlPtr dThPtr dTmLen dTsLen dTlLen dThLen Rro
      (pi + 1) j bp (o + 1) m' := by
  have hOk' : ∀ t < o + 1, MonoSliceOk srcPool
      ((dTm.set o (qm.getD a.toNat 0#32)).getD t 0#32).toNat ptop ∧
      (srcPool.getD ((dTm.set o (qm.getD a.toNat 0#32)).getD t 0#32).toNat
        0#32).toNat + 1 < 2 ^ 32 := by
    intro t ht; rw [getD_set_eq dTm 0#32 _ ho_len]
    by_cases hto : t = o
    · simp only [hto, ↓reduceIte]; exact hQmOk a.toNat ha_lt
    · simp only [hto, ↓reduceIte]; exact hOk t (by omega)
  have hSorted' : ∀ t < o + 1, MonoSorted srcPool
      ((dTm.set o (qm.getD a.toNat 0#32)).getD t 0#32).toNat := by
    intro t ht; rw [getD_set_eq dTm 0#32 _ ho_len]
    by_cases hto : t = o
    · simp only [hto, ↓reduceIte]; exact hQmSorted a.toNat ha_lt
    · simp only [hto, ↓reduceIte]; exact hSorted t (by omega)
  have hSig' : SigOk srcPool (dTm.set o (qm.getD a.toNat 0#32)) (dTs.set o qs_a) (o + 1) := by
    intro t ht x hx
    rw [getD_set_eq dTm 0#32 _ ho_len] at hx
    rw [getD_set_eq dTs 0#64 _ hos]
    by_cases hto : t = o
    · simp only [hto, ↓reduceIte, hqs_eq] at hx ⊢; exact hQmSig a.toNat ha_lt x hx
    · simp only [hto, ↓reduceIte] at hx ⊢; exact hSig t (by omega) x hx
  have hwords' : monoTotalWords srcPool (dTm.set o (qm.getD a.toNat 0#32)) (o + 1) +
      tailWordSum srcPool srcTm j tn + tailQWordSum srcPool qm ixS (pi + 1) k ≤
      monoTotalWords srcPool srcTm tn + tailQWordSum srcPool qm ixS 0 k := by
    rw [monoTotalWords_set_eq ho_len, ha_eq]
    rw [tailQWordSum_split hpi] at hwords; omega
  have hSrcT' : ∀ t < o + 1,
      (∃ idx < tn, (dTm.set o (qm.getD a.toNat 0#32)).getD t 0#32 = srcTm.getD idx 0#32) ∨
      (∃ qidx < qn, (dTm.set o (qm.getD a.toNat 0#32)).getD t 0#32 = qm.getD qidx 0#32) := by
    intro t ht; rw [getD_set_eq dTm 0#32 _ ho_len]
    by_cases hto : t = o
    · simp only [hto, ↓reduceIte]; exact Or.inr ⟨a.toNat, ha_lt, rfl⟩
    · simp only [hto, ↓reduceIte]; exact hSrcT t (by omega)
  have heval' : ∀ σ : Nat → Bool,
      polyEval nOut σ srcPool (dTm.set o (qm.getD a.toNat 0#32))
        (dTl.set o ql_a) (dTh.set o qh_a) (o + 1) =
        nonBxRangeSum nOut σ srcPool srcTm srcTl srcTh bx nb 0 j +
          polyEvalIdxOf nOut σ srcPool qm qlS qhS ixS 0 (pi + 1) := fun σ => by
    rw [polyEval_set_eq ho_len hol hoh, polyEvalIdxOf_succ, Nat.zero_add, ← ha_eq, hql_eq,
      hqh_eq, heval σ]
    simp only [termEval]; ac_rfl
  exact ⟨dTm.set o (qm.getD a.toNat 0#32), dTs.set o qs_a, dTl.set o ql_a, dTh.set o qh_a,
    by simp [hdTm], by simp [hdTs], by simp [hdTl], by simp [hdTh],
    by omega, hbp, hj_tn, by omega, hlo, hhi, hOk', hSorted', hSig', hwords', hSrcT', heval', hm'⟩

end

/-! ## 4. `ar_merge_products_wp` (`Arisca.Src.Poly`) -/

@[expose] public def skip4L64 (v : Val i64) (cont : Expr Val Cont [] → Expr Val Cont [])
    (e : Expr Val Cont []) : Expr Val Cont [] :=
  match e with
  | @Expr.let_ _ _ _ [.bits 64] _ k1 => match k1 (0#64, ()) with
    | @Expr.let_ _ _ _ [.bits 64] _ k2 => match k2 (0#64, ()) with
      | @Expr.let_ _ _ _ [.bits 64] _ k3 => match k3 (0#64, ()) with
        | @Expr.let_ _ _ _ [.bits 64] _ k4 => match k4 (0#64, ()) with
          | @Expr.load _ _ _ (.bits 64) _ k5 => cont (k5 v)
          | _ => .ret ()
        | _ => .ret ()
      | _ => .ret ()
    | _ => .ret ()
  | _ => .ret ()

@[expose] public def mergeOuterExpr (cx : Val i64) (nb k sidx didx : Val i32)
    (sm ss sl sh dm ds dl dh pool bxPtr : Val i64) (n : Val i32)
    (JExit : Cont [i32, i32, i32, i32]) : Expr Val Cont [] :=
  match ar_merge_products_body Val Cont (cx, nb, ()) with
  | .call (bs := [.bits 32]) _ _ k0 => match k0 (k, ()) with
    | @Expr.let_ _ _ _ [.bits 64] _ k1 => match k1 (0#64, ()) with
      | @Expr.load _ _ _ (.bits 32) _ k2 => match k2 sidx with
        | @Expr.let_ _ _ _ [.bits 64] _ k3 => match k3 (0#64, ()) with
          | @Expr.load _ _ _ (.bits 32) _ k4 => match k4 sidx with
            | @Expr.let_ _ _ _ [.bits 32] _ k5 => match k5 (didx, ()) with
              | e6 =>
                skip4L64 sm (skip4L64 ss (skip4L64 sl (skip4L64 sh
                  (skip4L64 dm (skip4L64 ds (skip4L64 dl (skip4L64 dh fun e46 =>
                    match e46 with
                    | @Expr.let_ _ _ _ [.bits 64] _ k46 => match k46 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ k47 => match k47 (0#64, ()) with
                        | @Expr.load _ _ _ (.bits 32) _ k48 => match k48 0#32 with
                          | @Expr.let_ _ _ _ [.bits 64] _ k49 => match k49 (0#64, ()) with
                            | @Expr.let_ _ _ _ [.bits 64] _ k50 => match k50 (0#64, ()) with
                              | @Expr.let_ _ _ _ [.bits 64] _ k51 => match k51 (0#64, ()) with
                                | @Expr.load _ _ _ (.bits 64) _ k52 => match k52 pool with
                                  | @Expr.let_ _ _ _ [.bits 64] _ k53 => match k53 (0#64, ()) with
                                    | @Expr.load _ _ _ (.bits 64) _ k54 => match k54 bxPtr with
                                      | @Expr.let_ _ _ _ [.bits 64] _ k55 =>
                                        match k55 (0#64, ()) with
                                        | @Expr.load _ _ _ (.bits 32) _ k56 => match k56 n with
                                          | @Expr.group _ _ _
                                              [[.bits 32, .bits 32, .bits 32, .bits 32]] _ k57 =>
                                            k57 (JExit, ())
                                          | _ => .ret ()
                                        | _ => .ret ()
                                      | _ => .ret ()
                                    | _ => .ret ()
                                  | _ => .ret ()
                                | _ => .ret ()
                              | _ => .ret ()
                            | _ => .ret ()
                          | _ => .ret ()
                        | _ => .ret ()
                      | _ => .ret ()
                    | _ => .ret ()))))))) e6
            | _ => .ret ()
          | _ => .ret ()
        | _ => .ret ()
      | _ => .ret ()
    | _ => .ret ()
  | _ => .ret ()

@[expose] public def mergeLoopThenExpr (cx : Val i64) (nb k sidx didx : Val i32)
    (sm ss sl sh dm ds dl dh pool bxPtr : Val i64) (n : Val i32)
    (JExit JL : Cont [i32, i32, i32, i32]) (o cur bp pi : Val i32) : Expr Val Cont [] :=
  match mergeOuterExpr cx nb k sidx didx sm ss sl sh dm ds dl dh pool bxPtr n JExit with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 32, .bits 32]] bsL _ =>
    match bsL (JL, ()) with
    | .cons bL _ => match bL (o, cur, bp, pi, ()) with
      | @Expr.let_ _ _ _ [.bool] _ kCmp => match kCmp (false, ()) with
        | .jnz _ eLoop _ => eLoop
        | _ => .ret ()
      | _ => .ret ()
    | _ => .ret ()
  | _ => .ret ()

@[expose] public def mergeCopyLoopExpr (cx : Val i64) (nb k sidx didx : Val i32)
    (sm ss sl sh dm ds dl dh pool bxPtr : Val i64) (n : Val i32)
    (JExit JL : Cont [i32, i32, i32, i32]) (o cur bp pi : Val i32)
    (JA : Cont [i32, i32, i64]) (a j : Val i32) (qmPtr : Val i64) : Expr Val Cont [] :=
  match mergeLoopThenExpr cx nb k sidx didx sm ss sl sh dm ds dl dh pool bxPtr n
      JExit JL o cur bp pi with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 64]] bs2 _ =>
    match bs2 (JA, ()) with
    | .cons b2 _ => b2 (a, j, qmPtr, ())
    | _ => .ret ()
  | _ => .ret ()

@[expose] public def mergeCopyStepExpr (cx : Val i64) (nb k sidx didx : Val i32)
    (sm ss sl sh dm ds dl dh pool bxPtr : Val i64) (n : Val i32)
    (JExit JL : Cont [i32, i32, i32, i32]) (o cur bp pi : Val i32)
    (JA : Cont [i32, i32, i64]) (a j : Val i32) (qmPtr : Val i64)
    (JC : Cont [i32, i32, i32]) (oC curC bpC : Val i32) : Expr Val Cont [] :=
  match mergeCopyLoopExpr cx nb k sidx didx sm ss sl sh dm ds dl dh pool bxPtr n
      JExit JL o cur bp pi JA a j qmPtr with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 32]] bs3 _ =>
    match bs3 (JC, ()) with
    | .cons b3 _ => match b3 (oC, curC, bpC, ()) with
      | @Expr.let_ _ _ _ [.bool] _ kC => match kC (false, ()) with
        | .jnz _ eCopy _ => eCopy
        | _ => .ret ()
      | _ => .ret ()
    | _ => .ret ()
  | _ => .ret ()

@[expose] public def mergeEmitExpr (cx : Val i64) (nb k sidx didx : Val i32)
    (sm ss sl sh dm ds dl dh pool bxPtr : Val i64) (n : Val i32)
    (JExit JL : Cont [i32, i32, i32, i32]) (o cur bp pi : Val i32)
    (JA : Cont [i32, i32, i64]) (a j : Val i32) (qmPtr : Val i64)
    (JC : Cont [i32, i32, i32]) (oC curC bpC : Val i32) : Expr Val Cont [] :=
  match mergeCopyLoopExpr cx nb k sidx didx sm ss sl sh dm ds dl dh pool bxPtr n
      JExit JL o cur bp pi JA a j qmPtr with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 32]] bs3 _ =>
    match bs3 (JC, ()) with
    | .cons b3 _ => match b3 (oC, curC, bpC, ()) with
      | @Expr.let_ _ _ _ [.bool] _ kC => match kC (false, ()) with
        | .jnz _ _ eFalse => match eFalse with
          | @Expr.let_ _ _ _ [.bool] _ kEq => match kEq (false, ()) with
            | .jnz _ _ eEmit => eEmit
            | _ => .ret ()
          | _ => .ret ()
        | _ => .ret ()
      | _ => .ret ()
    | _ => .ret ()
  | _ => .ret ()

public theorem merge_products_copy_step (Γ : T.Env)
    {cx sm ss sl sh dm ds dl dh pool bxPtr qmPtr : Val i64}
    {nb k sidx didx n o cur bp pi a j oC curC bpC : Val i32}
    {Q : Post []} {X : XPost} {s sSort : ArCtxState}
    {srcPool srcTm qm ixS bx dstTm0 : List (BitVec 32)}
    {qs srcTs srcTl srcTh qlS qhS dstTs0 dstTl0 dstTh0 : List (BitVec 64)}
    {dTmC : List (BitVec 32)} {dTsC dTlC dThC : List (BitVec 64)}
    {restM R Rro : Mem 64 → Prop}
    {JExit JL : Cont [i32, i32, i32, i32]} {JA : Cont [i32, i32, i64]}
    {JC : Cont [i32, i32, i32]} {mC : Mem 64}
    (hrecC : ∀ (crem' : Nat) (ys : Tup Val [i32, i32, i32]) (m' : Mem 64),
      crem' < j.toNat - curC.toNat →
      (crem' = j.toNat - ys.2.1.toNat ∧ cur.toNat ≤ ys.2.1.toNat ∧ ys.2.1.toNat ≤ j.toNat ∧
        MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.modW s.ptop.toNat
          srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
          (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
          (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
          dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
          pi.toNat ys.2.1.toNat ys.2.2.1.toNat ys.1.toNat m') →
      JC ys m')
    (hsm : sm = s.tm.getD s.tc.toNat 0#64) (hss : ss = s.ts.getD s.tc.toNat 0#64)
    (hsl : sl = s.tl.getD s.tc.toNat 0#64) (hsh : sh = s.th.getD s.tc.toNat 0#64)
    (hdm : dm = s.tm.getD (1 - s.tc.toNat) 0#64)
    (hds : ds = s.ts.getD (1 - s.tc.toNat) 0#64)
    (hdl : dl = s.tl.getD (1 - s.tc.toNat) 0#64)
    (hdh : dh = s.th.getD (1 - s.tc.toNat) 0#64)
    (hbxPtr : bxPtr = s.bx)
    (hRro : Rro = arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
      array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
      array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
      array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆ array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
      array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆ array64 s.qh qhS ⋆
      array (t := i32) sSort.ix ixS ⋆ array (t := i32) s.bx bx ⋆ restM ⋆ R)
    (htn_le : s.tn.toNat ≤ s.tcap.toNat) (hk_qn : k.toNat ≤ s.qn.toNat)
    (hcap_sum : (s.tn.toNat - nb.toNat) + s.qn.toNat ≤ s.tcap.toNat)
    (hnb_bx : nb.toNat ≤ bx.length) (hinc : strictIncBelow bx nb.toNat s.tn.toNat)
    (hsrcTm_len : s.tcap.toNat ≤ srcTm.length) (hsrcTs_len : s.tcap.toNat ≤ srcTs.length)
    (hsrcTl_len : s.tcap.toNat ≤ srcTl.length) (hsrcTh_len : s.tcap.toNat ≤ srcTh.length)
    (hTmOk : ∀ t < s.tn.toNat, MonoSliceOk srcPool (srcTm.getD t 0#32).toNat s.ptop.toNat ∧
      (srcPool.getD (srcTm.getD t 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hTmSorted : ∀ t < s.tn.toNat, MonoSorted srcPool (srcTm.getD t 0#32).toNat)
    (hTmSig : SigOk srcPool srcTm srcTs s.tn.toNat)
    (hcur_C : cur.toNat ≤ curC.toNat) (hcurC_lt : curC.toNat < j.toNat)
    (hj_tn : j.toNat ≤ s.tn.toNat)
    (hdC1 : dTmC.length = dstTm0.length) (hdC2 : dTsC.length = dstTs0.length)
    (hdC3 : dTlC.length = dstTl0.length) (hdC4 : dThC.length = dstTh0.length)
    (hdstTm_len : s.tcap.toNat ≤ dstTm0.length) (hdstTs_len : s.tcap.toNat ≤ dstTs0.length)
    (hdstTl_len : s.tcap.toNat ≤ dstTl0.length) (hdstTh_len : s.tcap.toNat ≤ dstTh0.length)
    (hpi_k : pi.toNat ≤ k.toNat) (hbpC_nb : bpC.toNat ≤ nb.toNat)
    (hcurC_tn : curC.toNat ≤ s.tn.toNat) (hoC_le : oC.toNat ≤ curC.toNat - bpC.toNat + pi.toNat)
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
      polyEval s.modW σ srcPool dTmC dTlC dThC oC.toNat =
        nonBxRangeSum s.modW σ srcPool srcTm srcTl srcTh bx nb.toNat 0 curC.toNat +
          polyEvalIdxOf s.modW σ srcPool qm qlS qhS ixS 0 pi.toNat)
    (hmC : (array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmC ⋆
      array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsC ⋆
      array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlC ⋆
      array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThC ⋆ Rro) mC) :
    wp Γ Q X (mergeCopyStepExpr cx nb k sidx didx sm ss sl sh dm ds dl dh pool bxPtr n
      JExit JL o cur bp pi JA a j qmPtr JC oC curC bpC) mC := by
  rw [hsm, hss, hsl, hsh, hdm, hds, hdl, hdh, hbxPtr]
  dsimp only [mergeCopyStepExpr, mergeCopyLoopExpr, mergeLoopThenExpr, mergeOuterExpr, skip4L64]
  refine wp_join_group (fun (v : Tup Val [i32]) mE =>
      let (e, _) := v
      mE = mC ∧ curC.toNat ≤ e.toNat ∧ e.toNat ≤ j.toNat ∧
      (e.toNat < j.toNat → bpC.toNat < nb.toNat ∧ e = bx.getD bpC.toNat 0#32) ∧
      (bpC.toNat < nb.toNat → e.toNat ≤ (bx.getD bpC.toNat 0#32).toNat)) ?_ ?_
  · rintro JE ⟨e, ⟨⟩⟩ mE ⟨hmE, hcur_e, he_j, he_lt, he_hi⟩
    subst mE
    refine wp_loop_group (fun irem (v : Tup Val [i32, i32]) mI =>
        let (oI, iI, _) := v
        irem = e.toNat - iI.toNat ∧ curC.toNat ≤ iI.toNat ∧ iI.toNat ≤ e.toNat ∧
        MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.modW s.ptop.toNat
          srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
          (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
          (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
          dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
          pi.toNat iI.toNat bpC.toNat oI.toNat mI) ?_ ?_
    · intro JI irem ⟨oI, iI, ⟨⟩⟩ mI hrecI
        ⟨hirem, hcur_I, hiI_e, dTmI, dTsI, dTlI, dThI, hdI1, hdI2, hdI3, hdI4,
          _, hbpI_nb, hiI_tn, hoI_le, hloI, hhiI, hOkI, hSortedI, hSigI, hwordsI, hSrcTI,
          hevalI, hmI⟩
      c0_hsplit
      · have hiI_lt : iI.toNat < e.toNat := hc
        clear hc
        have hhiI1 : bpC.toNat < nb.toNat →
            iI.toNat + 1 ≤ (bx.getD bpC.toNat 0#32).toNat := fun h => by
          have := he_hi h; omega
        have hsub := strictIncBelow_cur_sub_bp hinc hbpI_nb (by omega : iI.toNat + 1 ≤ _)
          (fun p hp => Nat.lt_trans (hloI p hp) (Nat.lt_succ_self _)) hhiI1
        have hbp_le_iI : bpC.toNat ≤ iI.toNat :=
          (strictIncBelow_cur_sub_bp hinc hbpI_nb (by omega : iI.toNat ≤ _) hloI
            (fun h => by have := he_hi h; omega)).1
        have hoI_lt_cap : oI.toNat < s.tcap.toNat := by omega
        have hiI_p1 : (iI + 1#32).toNat = iI.toNat + 1 :=
          bv32_succ_toNat (by have := e.isLt; omega)
        have hoI_p1 : (oI + 1#32).toNat = oI.toNat + 1 := bv32_succ_toNat (by omega)
        have hoI64 : (BitVec.setWidth 64 oI).toNat = oI.toNat := by c0_bv_omega
        have hiI_tm : iI.toNat < srcTm.length := by omega
        have hiI_ts : iI.toNat < srcTs.length := by omega
        have hiI_tl : iI.toNat < srcTl.length := by omega
        have hiI_th : iI.toNat < srcTh.length := by omega
        have hmI0 : (array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmI ⋆
            array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsI ⋆
            array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlI ⋆
            array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThI ⋆ Rro) mI := hmI
        rw [hRro] at hmI0
        have hmI1 : (array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmI ⋆
            array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsI ⋆
            array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlI ⋆
            array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThI ⋆
            array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
            array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
            array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
            array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
            (arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
              array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆
              array64 s.qh qhS ⋆ array (t := i32) sSort.ix ixS ⋆
              array (t := i32) s.bx bx ⋆ restM ⋆ R)) mI :=
          sep_cast hmI0 (by ac_rfl)
        c0_hfast_nogrp
        refine hrecI (e.toNat - (iI + 1#32).toNat) (oI + 1#32, iI + 1#32, ⟨⟩) _
          (by rw [hiI_p1]; omega) ⟨rfl, by rw [hiI_p1]; omega, by rw [hiI_p1]; omega, ?_⟩
        rw [hiI_p1, hoI_p1]
        exact merge_copy_step hinc hnb_bx hTmOk hTmSorted hTmSig hdI1 hdI2 hdI3 hdI4
          hpi_k hbpI_nb (by omega) hoI_le (by omega) hloI hhiI1 hOkI hSortedI hSigI
          hwordsI hSrcTI hevalI
          (getD_eq_getElem srcTm 0#32 hiI_tm).symm
          (getD_eq_getElem srcTs 0#64 hiI_ts).symm
          (getD_eq_getElem srcTl 0#64 hiI_tl).symm
          (getD_eq_getElem srcTh 0#64 hiI_th).symm
          (by omega) (by omega) (by omega)
          (by have hiI64 : (BitVec.setWidth 64 iI).toNat = iI.toNat := by c0_bv_omega
              simp only [hoI64, hiI64] at hm
              exact sep_cast hm (by rw [hRro, ExtHashMap.sep_emp]; ac_rfl))
      · have hi_eq : iI = e := BitVec.eq_of_toNat_eq (by have := BitVec.not_lt.mp hc; omega)
        subst hi_eq; clear hc
        have hminv : MergeProdInv s.tn.toNat s.tn.toNat s.qn.toNat nb.toNat k.toNat s.modW
            s.ptop.toNat srcPool srcTm qm ixS bx srcTl srcTh qlS qhS
            (s.tm.getD (1 - s.tc.toNat) 0#64) (s.ts.getD (1 - s.tc.toNat) 0#64)
            (s.tl.getD (1 - s.tc.toNat) 0#64) (s.th.getD (1 - s.tc.toNat) 0#64)
            dstTm0.length dstTs0.length dstTl0.length dstTh0.length Rro
            pi.toNat iI.toNat bpC.toNat oI.toNat mI :=
          ⟨dTmI, dTsI, dTlI, dThI, hdI1, hdI2, hdI3, hdI4, hpi_k, hbpI_nb, hiI_tn,
            hoI_le, hloI, hhiI, hOkI, hSortedI, hSigI, hwordsI, hSrcTI, hevalI, hmI⟩
        refine wp_join_group (fun (v : Tup Val [i32, i32]) mN =>
            mN = mI ∧ v.1.toNat = (if iI.toNat < j.toNat then iI.toNat + 1 else j.toNat) ∧
            v.2.1.toNat = (if iI.toNat < j.toNat then bpC.toNat + 1 else bpC.toNat)) ?_ ?_
        · rintro JN ⟨cur', bp', ⟨⟩⟩ mN ⟨hmN, hcur'_eq, hbp'_eq⟩
          subst mN
          c0_hfast
          refine hrecC (j.toNat - cur'.toNat) (oI, cur', bp', ⟨⟩) mI
            (by rw [hcur'_eq]; split <;> omega)
            ⟨rfl, by rw [hcur'_eq]; split <;> omega, by rw [hcur'_eq]; split <;> omega, ?_⟩
          rw [hcur'_eq, hbp'_eq]
          exact merge_skip_bx_step hinc hnb_bx hj_tn he_j hminv
            (fun h => ⟨(he_lt h).1, (congrArg BitVec.toNat (he_lt h).2).symm⟩)
        · intro JN hJN
          c0_hsplit
          · have hlt : iI.toNat < j.toNat := hc
            have hbp_lt : bpC.toNat < nb.toNat := (he_lt hlt).1
            have hep1 : (iI + 1#32).toNat = iI.toNat + 1 :=
              bv32_succ_toNat (by have := j.isLt; omega)
            have hbp1 : (bpC + 1#32).toNat = bpC.toNat + 1 :=
              bv32_succ_toNat (by have := nb.isLt; omega)
            c0_hfast
            exact hJN (iI + 1#32, bpC + 1#32, ⟨⟩) mI
              ⟨rfl, by simp [hlt, hep1], by simp [hlt, hbp1]⟩
          · have hnlt : ¬ iI.toNat < j.toNat := by c0_bv_omega
            c0_hfast
            exact hJN (j, bpC, ⟨⟩) mI ⟨rfl, by simp [hnlt], by simp [hnlt]⟩
    · intro JI hJI; c0_hfast; exact hJI (e.toNat - curC.toNat) (oC, curC, ⟨⟩) mC
        ⟨rfl, le_refl _, hcur_e, dTmC, dTsC, dTlC, dThC, hdC1, hdC2, hdC3, hdC4,
          hpi_k, hbpC_nb, hcurC_tn, hoC_le, hloC, hhiC, hOkC, hSortedC, hSigC,
          hwordsC, hSrcTC, hevalC, hmC⟩
  · intro JE hJE
    have hmC0 : (array (t := i32) s.bx bx ⋆
        (array (t := i32) (s.tm.getD (1 - s.tc.toNat) 0#64) dTmC ⋆
          array64 (s.ts.getD (1 - s.tc.toNat) 0#64) dTsC ⋆
          array64 (s.tl.getD (1 - s.tc.toNat) 0#64) dTlC ⋆
          array64 (s.th.getD (1 - s.tc.toNat) 0#64) dThC ⋆
          arCtxMem cx sSort ⋆ array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
          array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
          array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
          array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
          array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
          array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql qlS ⋆
          array64 s.qh qhS ⋆ array (t := i32) sSort.ix ixS ⋆ restM ⋆ R)) mC := by
      rw [hRro] at hmC; exact sep_cast hmC (by ac_rfl)
    c0_hsplit
    · have hbp_lt : bpC.toNat < nb.toNat := hc; clear hc
      have hbp_bx : bpC.toNat < bx.length := by omega
      have hbp64 : (BitVec.setWidth 64 bpC).toNat = bpC.toNat := by c0_bv_omega
      c0_hsplit
      · have hbx_lt : (bx[(BitVec.setWidth 64 bpC).toNat]'(by
            simpa [hbp64] using hbp_bx)).toNat < j.toNat := hc
        clear hc
        have hbx_eq : bx[(BitVec.setWidth 64 bpC).toNat]'(by
            simpa [hbp64] using hbp_bx) = bx.getD bpC.toNat 0#32 := by
          simp only [hbp64]; exact (getD_eq_getElem bx 0#32 hbp_bx).symm
        c0_hfast
        refine hJE (bx[(BitVec.setWidth 64 bpC).toNat]'_, ⟨⟩) mC
          ⟨rfl, ?_, ?_, fun _ => ⟨hbp_lt, hbx_eq⟩, fun _ => by rw [hbx_eq]; exact le_refl _⟩
        · rw [hbx_eq]; exact hhiC hbp_lt
        · rw [hbx_eq, ← hbx_eq]; exact le_of_lt hbx_lt
      · have hbx_ge : j.toNat ≤ (bx.getD bpC.toNat 0#32).toNat := by
          have hnot := hc
          rw [← getD_eq_getElem bx 0#32 (by omega)] at hnot
          exact Nat.le_of_not_lt hnot
        c0_hfast
        exact hJE (j, ⟨⟩) mC ⟨rfl, le_of_lt hcurC_lt, le_refl _,
          fun h => absurd h (Nat.lt_irrefl _), fun _ => hbx_ge⟩
    · have hbp_eq : bpC.toNat = nb.toNat := by have := BitVec.not_lt.mp hc; omega
      c0_hfast
      exact hJE (j, ⟨⟩) mC ⟨rfl, le_of_lt hcurC_lt, le_refl _,
        fun h => absurd h (Nat.lt_irrefl _), fun h => by omega⟩


end LeanQbe.T.Examples.Arisca.Proof

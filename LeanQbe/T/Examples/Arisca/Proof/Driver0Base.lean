/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Src.Driver
public import LeanQbe.T.Examples.Arisca.Proof.Sem
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0StepAttr
meta import LeanQbe.T.Logic.C0StepAttr
import Kraken.Separation

/-!
# ARiSCA Truth-Table Sim & Dense 4-Var Polynomials (`Arisca.Proof.Driver0Base`)

`XPost`-polymorphic (`noExit = true`, `<= std3`) WP contracts and proofs for the first `7`
functions of `LeanQbe.T.Examples.Arisca.Src.Driver`:
Specs for all `7` functions (`arTtsimSpec`..`arMask6Spec`), pure invariants, and
WP proofs for `ar_mask6`, `ar_dzero`, `ar_dlit`, `ar_daxpy`, `ar_dmul`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Arisca.Proof

open Std
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Arisca (Aig xmask xmask_bit)
open LeanQbe.T.Examples.Arisca.Src
open LeanQbe.T.Examples.Arisca.Src.Driver

/-! ## 1. Pure Definitions & `XPost`-Polymorphic `Spec` Contracts -/

@[expose] public section

/-- Indicator that all variables present in 4-bit `mask` hold under `σ4`. -/
def denseMono (σ4 : Nat → Bool) (mask : Nat) : Bool :=
  (List.range 4).all (fun j => !mask.testBit j || σ4 j)

/-- Single term `d[mask]` of a 16-entry dense 4-variable polynomial (mod `2^64`). -/
def denseTerm64 (σ4 : Nat → Bool) (d : List (BitVec 64)) (mask : Nat) : BitVec 64 :=
  if denseMono σ4 mask then d.getD mask 0#64 else 0#64

/-- Evaluation of a 16-entry dense 4-variable polynomial mod `2^64`. -/
def denseEval64 (σ4 : Nat → Bool) (d : List (BitVec 64)) : BitVec 64 :=
  (List.range 16).foldl (fun acc mask => acc + denseTerm64 σ4 d mask) 0#64

/-- Fixed monomial-offset table `[0, 5, 10, ..., 75]` for `ar_dcanon` output in `gsy`. -/
def gsyMOff : List (BitVec 32) :=
  (List.range 16).map (fun i => BitVec.ofNat 32 (5 * i))

/-- Evaluation of a 16-entry dense 4-variable polynomial over `vs[0..3]` mod `2^nOut`. -/
def denseEvalNOut (nOut : Nat) (σ : Nat → Bool) (vs : List (BitVec 32))
    (d : List (BitVec 64)) : BitVec nOut :=
  (List.range 16).foldl (fun acc mask =>
    acc + if denseMono (fun j => σ (vs.getD j 0#32).toNat) mask then
      BitVec.ofInt nOut (d.getD mask 0#64).toInt else 0#nOut) 0#nOut

/-- Soundness invariant on `ar_ttsim` memo `(mn, mv)` over `0 .. nm - 1`. -/
def TtMemoOk (g : Aig) (nleaf : Nat) (lnode : List (BitVec 32)) (lmask : List (BitVec 64))
    (all : BitVec 64) (nm : Nat) (mn : List (BitVec 32)) (mv : List (BitVec 64)) : Prop :=
  ∀ (t : Nat) (ρ : Nat → Bool), t < 64 → all.toNat.testBit t = true →
    (∀ j < nleaf, (lmask.getD j 0#64).toNat.testBit t = g.nodeVal ρ (lnode.getD j 0#32).toNat) →
    ∀ k < nm, (mv.getD k 0#64).toNat.testBit t = g.nodeVal ρ (mn.getD k 0#32).toNat

/-- Minimal slice-comparison spec for `ar_mcmp(a, b)` required by `ar_dcanon`. -/
def arMcmpSliceSpec : Spec [i64, i64] [i32] :=
  fun ⟨a, b, ⟨⟩⟩ m Q _ =>
    ∃ (ma mb : List (BitVec 32)) (R : Mem 64 → Prop), MonoSliceOk ma 0 ma.length ∧
      MonoSliceOk mb 0 mb.length ∧ (ma.getD 0 0#32).toNat + 1 < 2 ^ 32 ∧
      (array (t := i32) a ma ⋆ array (t := i32) b mb ⋆ R) m ∧
      (∀ r : BitVec 32, (r = 0#32 → symListAt ma 0 = symListAt mb 0) → Q (r, ⟨⟩) m)

/-- WP specification for `ar_ttsim(cx, lit, nleaf, all)`. -/
def arTtsimSpec : Spec [i64, i32, i32, i64] [.bool, i64] :=
  fun ⟨cx, lit, nleaf, all, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (g : Aig) (rhs0 rhs1 olit : List (BitVec 32))
      (stkN stkP memoN : List (BitVec 32)) (memoV dense : List (BitVec 64))
      (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64)) (R : Mem 64 → Prop),
      s.I.toNat = g.I ∧ s.M.toNat = g.M ∧ AigRep g rhs0 rhs1 olit ∧
      nleaf.toNat ≤ 6 ∧ 160 ≤ stkN.length ∧ 160 ≤ stkP.length ∧
      64 ≤ memoN.length ∧ 64 ≤ memoV.length ∧ (arCtxMem cx s ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
       gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆ R) m ∧
      (∀ (ok : Bool) (v : BitVec 64)
         (stkN' stkP' memoN' : List (BitVec 32)) (memoV' : List (BitVec 64)) (m' : Mem 64),
         stkN'.length = stkN.length → stkP'.length = stkP.length →
         memoN'.length = memoN.length → memoV'.length = memoV.length →
         (ok = true → ∀ (t : Nat) (ρ : Nat → Bool), t < 64 → all.toNat.testBit t = true →
           (∀ j < nleaf.toNat, (s.g_lmask.getD j 0#64).toNat.testBit t =
               g.nodeVal ρ (s.g_lnode.getD j 0#32).toNat) →
           v.toNat.testBit t = g.litVal ρ lit.toNat) →
         (arCtxMem cx s ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
          gateScratchMem s stkN' stkP' memoN' memoV' dense gsy gcl gch ⋆ R) m' →
         Q (ok, v, ⟨⟩) m')

/-- WP specification for `ar_dzero(d)`. -/
def arDzeroSpec : Spec [i64] [] :=
  fun ⟨dPtr, ⟨⟩⟩ m Q _ =>
    ∃ (d : List (BitVec 64)) (R : Mem 64 → Prop), 16 ≤ d.length ∧
      (array64 dPtr d ⋆ R) m ∧ (∀ (d' : List (BitVec 64)) (m' : Mem 64),
        d'.length = d.length → d'.drop 16 = d.drop 16 → (∀ i < 16, d'.getD i 0#64 = 0#64) →
        (∀ σ4 : Nat → Bool, denseEval64 σ4 d' = 0#64) → (array64 dPtr d' ⋆ R) m' → Q () m')

/-- WP specification for `ar_dlit(d, j, neg)`. -/
def arDlitSpec : Spec [i64, i32, i32] [] :=
  fun ⟨dPtr, j, neg, ⟨⟩⟩ m Q _ =>
    ∃ (d : List (BitVec 64)) (R : Mem 64 → Prop), 16 ≤ d.length ∧ j.toNat < 4 ∧
      (array64 dPtr d ⋆ R) m ∧ (∀ (d' : List (BitVec 64)) (m' : Mem 64),
        d'.length = d.length → d'.drop 16 = d.drop 16 → (∀ σ4 : Nat → Bool, denseEval64 σ4 d' =
          if neg ≠ 0#32 then 1#64 - (if σ4 j.toNat then 1#64 else 0#64)
          else (if σ4 j.toNat then 1#64 else 0#64)) →
        (array64 dPtr d' ⋆ R) m' → Q () m')

/-- WP specification for `ar_dmul(a, b, c)`. -/
def arDmulSpec : Spec [i64, i64, i64] [] :=
  fun ⟨pa, pb, pc, ⟨⟩⟩ m Q _ =>
    ∃ (a b c : List (BitVec 64)) (R : Mem 64 → Prop),
      16 ≤ a.length ∧ 16 ≤ b.length ∧ 16 ≤ c.length ∧
      (array64 pa a ⋆ array64 pb b ⋆ array64 pc c ⋆ R) m ∧ (∀ (c' : List (BitVec 64)) (m' : Mem 64),
        c'.length = c.length → c'.drop 16 = c.drop 16 →
        (∀ σ4 : Nat → Bool, denseEval64 σ4 c' = denseEval64 σ4 a * denseEval64 σ4 b) →
        (array64 pa a ⋆ array64 pb b ⋆ array64 pc c' ⋆ R) m' → Q () m')

/-- WP specification for `ar_daxpy(y, k, x)`. -/
def arDaxpySpec : Spec [i64, i64, i64] [] :=
  fun ⟨py, k, px, ⟨⟩⟩ m Q _ =>
    ∃ (y x : List (BitVec 64)) (R : Mem 64 → Prop), 16 ≤ y.length ∧ 16 ≤ x.length ∧
      (array64 py y ⋆ array64 px x ⋆ R) m ∧ (∀ (y' : List (BitVec 64)) (m' : Mem 64),
        y'.length = y.length → y'.drop 16 = y.drop 16 →
        (∀ i < 16, y'.getD i 0#64 = y.getD i 0#64 + k * x.getD i 0#64) →
        (∀ σ4 : Nat → Bool, denseEval64 σ4 y' = denseEval64 σ4 y + k * denseEval64 σ4 x) →
        (array64 py y' ⋆ array64 px x ⋆ R) m' → Q () m')

/-- WP specification for `ar_dcanon(cx, D)`. -/
def arDcanonSpec : Spec [i64, i64] [i32] :=
  fun ⟨cx, dPtr, ⟨⟩⟩ m Q _ =>
    ∃ (s : ArCtxState) (d gcl gch : List (BitVec 64)) (gsy : List (BitVec 32))
      (R : Mem 64 → Prop), MasksOk s.modW s.mlo s.mhi ∧
      16 ≤ d.length ∧ 85 ≤ gsy.length ∧ 16 ≤ gcl.length ∧ 16 ≤ gch.length ∧
      (arCtxMem cx s ⋆ array64 dPtr d ⋆ arrayPad i32 s.gsy gsy ⋆
       array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ R) m ∧
      (∀ (k : BitVec 32) (gsy' : List (BitVec 32)) (gcl' gch' : List (BitVec 64))
         (m' : Mem 64), k.toNat ≤ 16 →
         gsy'.length = gsy.length → gcl'.length = gcl.length → gch'.length = gch.length →
         (∀ i < k.toNat, MonoSliceOk gsy' (5 * i) 80 ∧ (gsy'.getD (5 * i) 0#32).toNat ≤ 4 ∧
           ∀ sym ∈ symListAt gsy' (5 * i), ∃ j < 4, sym = (s.g_vs.getD j 0#32).toNat) →
         (∀ i < k.toNat, MonoSorted gsy' (5 * i)) →
         (∀ σ : Nat → Bool, polyEval s.modW σ gsy' gsyMOff gcl' gch' k.toNat =
             denseEvalNOut s.modW σ s.g_vs d) →
         (arCtxMem cx s ⋆ array64 dPtr d ⋆ arrayPad i32 s.gsy gsy' ⋆
          array64 s.gcl gcl' ⋆ array64 s.gch gch' ⋆ R) m' →
         Q (k, ⟨⟩) m')

/-- WP specification for `ar_mask6(j)`. -/
def arMask6Spec : Spec [i32] [i64] :=
  fun ⟨j, ⟨⟩⟩ m Q _ =>
    j.toNat < 6 ∧ Q (BitVec.ofNat 64 (xmask j.toNat), ⟨⟩) m

end

/-! ## 2. Pure Dense-Polynomial & List Helpers -/

public section

theorem d_getD_eq_getElem {α : Type _} (xs : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : xs.getD i d = xs[i] := by simp [List.getD_eq_getElem?_getD, hi]

theorem d_getD_set_eq {α : Type _} (xs : List α) (d v : α) {i : Nat}
    (hi : i < xs.length) : (xs.set i v).getD i d = v := by simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_ne {α : Type _} (xs : List α) (d v : α) {i j : Nat}
    (hne : j ≠ i) : (xs.set i v).getD j d = xs.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]

theorem bv32_add1_toNat {v : BitVec 32} (h : v.toNat + 1 < 2 ^ 32) :
    (v + 1).toNat = v.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

theorem bv32_sub1_toNat {v : BitVec 32} (h : 1 ≤ v.toNat) :
    (v - 1).toNat = v.toNat - 1 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by simpa using h)),
    show (1 : BitVec 32).toNat = 1 from rfl]

theorem bv32_mul5_toNat {v : BitVec 32} (h : 5 * v.toNat < 2 ^ 32) :
    (5 * v).toNat = 5 * v.toNat := by
  rw [BitVec.toNat_mul, show (5 : BitVec 32).toNat = 5 from rfl, Nat.mod_eq_of_lt h]

theorem bv32_mul5_r_toNat {v : BitVec 32} (h : 5 * v.toNat < 2 ^ 32) :
    (v * 5).toNat = 5 * v.toNat := by
  rw [BitVec.toNat_mul, show (5 : BitVec 32).toNat = 5 from rfl, Nat.mul_comm, Nat.mod_eq_of_lt h]
theorem bv64_sw_toNat {v : BitVec 32} : (BitVec.setWidth 64 v).toNat = v.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans v.isLt (by decide))]
private theorem denseMono_iff (σ4 : Nat → Bool) (mask : Nat) :
    denseMono σ4 mask = true ↔ ∀ j < 4, mask.testBit j = true → σ4 j = true := by
  simp only [denseMono, List.all_eq_true, List.mem_range]
  exact ⟨fun h j hj hb => by simpa [hb] using h j hj,
    fun h j hj => by cases hb : mask.testBit j <;> simp [h j hj, hb]⟩
private theorem denseMono_zero (σ4 : Nat → Bool) : denseMono σ4 0 = true := by
  rw [denseMono_iff]; intro j _ h; simp at h
private theorem denseMono_two_pow (σ4 : Nat → Bool) {j : Nat} (hj : j < 4) :
    denseMono σ4 (2 ^ j) = σ4 j := by
  cases h : σ4 j
  · rw [Bool.eq_false_iff]; intro ht
    have := (denseMono_iff σ4 (2 ^ j)).mp ht j hj (by simp); rw [h] at this; cases this
  · rw [denseMono_iff]; intro k _ hb
    obtain rfl : j = k := by simpa [Nat.testBit_two_pow] using hb
    exact h
private theorem denseMono_or {σ4 : Nat → Bool} {a b : Nat} :
    denseMono σ4 (a ||| b) = (denseMono σ4 a && denseMono σ4 b) := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [Bool.and_eq_true, denseMono_iff, Nat.testBit_or, Bool.or_eq_true]
  exact ⟨fun h => ⟨fun j hj ha => h j hj (Or.inl ha), fun j hj hb => h j hj (Or.inr hb)⟩,
    fun ⟨ha, hb⟩ j hj h => h.elim (ha j hj) (hb j hj)⟩
private theorem denseTerm64_or_mul (σ4 : Nat → Bool) (a b : List (BitVec 64)) (i j : Nat) :
    (if denseMono σ4 (i ||| j) then a.getD i 0#64 * b.getD j 0#64 else 0#64) =
      denseTerm64 σ4 a i * denseTerm64 σ4 b j := by
  rw [denseMono_or]; unfold denseTerm64
  cases denseMono σ4 i <;> cases denseMono σ4 j <;> simp
private theorem range_foldl_add_succ {w : Nat} (f : Nat → BitVec w) (n : Nat) :
    (List.range (n + 1)).foldl (fun acc k => acc + f k) 0#w =
      (List.range n).foldl (fun acc k => acc + f k) 0#w + f n := by simp [List.range_succ]
private theorem range_foldl_add_congr {w : Nat} {f g : Nat → BitVec w} (n : Nat)
    (h : ∀ k < n, f k = g k) :
    (List.range n).foldl (fun acc k => acc + f k) 0#w =
      (List.range n).foldl (fun acc k => acc + g k) 0#w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [range_foldl_add_succ, range_foldl_add_succ,
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]
private theorem range_foldl_add_eq_zero {w : Nat} (f : Nat → BitVec w) (n : Nat)
    (h : ∀ k < n, f k = 0#w) :
    (List.range n).foldl (fun acc k => acc + f k) 0#w = 0#w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [range_foldl_add_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
      h n (Nat.lt_succ_self n), BitVec.add_zero]
private theorem range_foldl_set_add {w : Nat} (f g : Nat → BitVec w) (n idx : Nat) (v : BitVec w)
    (hidx : idx < n) (heq : ∀ k < n, g k = if k = idx then f k + v else f k) :
    (List.range n).foldl (fun acc k => acc + g k) 0#w =
      (List.range n).foldl (fun acc k => acc + f k) 0#w + v := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [range_foldl_add_succ, range_foldl_add_succ]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hidx) with hlast | hlt
    · rw [range_foldl_add_congr m (fun k hk => by
        rw [heq k (Nat.lt_succ_of_lt hk), ite_eq_right (by omega)])]
      rw [heq m (Nat.lt_succ_self m), hlast, ite_eq_left rfl, BitVec.add_assoc]
    · rw [ih hlt (fun k hk => heq k (Nat.lt_succ_of_lt hk)),
        heq m (Nat.lt_succ_self m), ite_eq_right (by omega),
        BitVec.add_assoc, BitVec.add_comm v (f m), ← BitVec.add_assoc]
private theorem denseEval64_set_add (σ4 : Nat → Bool) (d : List (BitVec 64))
    {idx : Nat} (hidx : idx < 16) (hlen : 16 ≤ d.length) (v : BitVec 64) :
    denseEval64 σ4 (d.set idx (d.getD idx 0#64 + v)) =
      denseEval64 σ4 d + (if denseMono σ4 idx then v else 0#64) := by
  unfold denseEval64
  refine range_foldl_set_add _ _ 16 idx _ hidx fun k hk => ?_
  by_cases hki : k = idx
  · subst hki; simp only [denseTerm64, d_getD_set_eq d 0#64 _ (i := k) (by omega), ↓reduceIte]
    cases denseMono σ4 k <;> simp
  · simp only [denseTerm64, getD_set_ne d 0#64 _ hki, ite_eq_right hki]
private theorem denseEval64_zero (σ4 : Nat → Bool) (d : List (BitVec 64))
    (h : ∀ i < 16, d.getD i 0#64 = 0#64) : denseEval64 σ4 d = 0#64 := by
  refine range_foldl_add_eq_zero _ 16 fun k hk => ?_
  unfold denseTerm64; rw [h k hk]; cases denseMono σ4 k <;> rfl
private theorem range_foldl_one_nonzero {w : Nat} (f : Nat → BitVec w) (n idx : Nat)
    (hidx : idx < n) (h0 : ∀ k < n, k ≠ idx → f k = 0#w) :
    (List.range n).foldl (fun acc k => acc + f k) 0#w = f idx := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [range_foldl_add_succ]
    by_cases h : idx = n
    · subst h; rw [range_foldl_add_eq_zero _ idx (fun k hk => h0 k (by omega) (by omega)),
        BitVec.zero_add]
    · rw [ih (by omega) (fun k hk hne => h0 k (by omega) hne), h0 n (by omega) (by omega),
        BitVec.add_zero]
private theorem range_foldl_two_nonzero {w : Nat} (f : Nat → BitVec w) (n i1 i2 : Nat)
    (hi1 : i1 < n) (hi2 : i2 < n) (hne : i1 ≠ i2) (h0 : ∀ k < n, k ≠ i1 → k ≠ i2 → f k = 0#w) :
    (List.range n).foldl (fun acc k => acc + f k) 0#w = f i1 + f i2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [range_foldl_add_succ]
    by_cases h1 : i1 = n
    · subst h1; rw [range_foldl_one_nonzero f i1 i2 (by omega)
        (fun k hk hk2 => h0 k (by omega) (by omega) hk2), BitVec.add_comm]
    · by_cases h2 : i2 = n
      · subst h2; rw [range_foldl_one_nonzero f i2 i1 (by omega)
          (fun k hk hk1 => h0 k (by omega) hk1 (by omega))]
      · rw [ih (by omega) (by omega) (fun k hk => h0 k (by omega)), h0 n (by omega) (by omega)
          (by omega), BitVec.add_zero]
private theorem two_pow_lt_16 {j : Nat} (hj : j < 4) : 2 ^ j < 16 := by
  have : 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega); omega
private theorem two_pow_ne_zero (j : Nat) : 2 ^ j ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
private theorem denseEval64_lit_pos (σ4 : Nat → Bool) (d : List (BitVec 64)) {j : Nat} (hj : j < 4)
    (h1 : d.getD (2 ^ j) 0#64 = 1#64) (h0 : ∀ k < 16, k ≠ 2 ^ j → d.getD k 0#64 = 0#64) :
    denseEval64 σ4 d = if σ4 j then 1#64 else 0#64 := by
  unfold denseEval64
  rw [range_foldl_one_nonzero _ 16 (2 ^ j) (two_pow_lt_16 hj) (fun k hk hne => by
    unfold denseTerm64; rw [h0 k hk hne]; cases denseMono σ4 k <;> rfl)]
  simp only [denseTerm64, denseMono_two_pow σ4 hj, h1]
private theorem denseEval64_lit_neg (σ4 : Nat → Bool) (d : List (BitVec 64)) {j : Nat} (hj : j < 4)
    (hz : d.getD 0 0#64 = 1#64) (h1 : d.getD (2 ^ j) 0#64 = -1#64)
    (h0 : ∀ k < 16, k ≠ 0 → k ≠ 2 ^ j → d.getD k 0#64 = 0#64) :
    denseEval64 σ4 d = 1#64 - (if σ4 j then 1#64 else 0#64) := by
  unfold denseEval64
  rw [range_foldl_two_nonzero _ 16 0 (2 ^ j) (by decide) (two_pow_lt_16 hj)
    (two_pow_ne_zero j).symm (fun k hk hne0 hnej => by
      unfold denseTerm64; rw [h0 k hk hne0 hnej]; cases denseMono σ4 k <;> rfl)]
  simp only [denseTerm64, denseMono_zero, ↓reduceIte, hz, denseMono_two_pow σ4 hj, h1]
  cases σ4 j <;> simp [BitVec.sub_eq_add_neg]

/-! ## 3. WP Proofs: `ar_mask6`, `ar_dzero`, `ar_dlit`, `ar_daxpy`, `ar_dmul` -/

theorem ar_mask6_wp (Γ : LeanQbe.T.Env) :
    ∀ xs m Q X, arMask6Spec xs m Q X → Func.wp Γ ar_mask6_body xs m Q X := by
  rintro ⟨j, ⟨⟩⟩ m Q X ⟨hj, hQ⟩
  c0_hsteps
  · subst hc; exact hQ
  · subst hc; exact hQ
  · subst hc; exact hQ
  · subst hc; exact hQ
  · subst hc; exact hQ
  · have hj5 : j = 5#32 := BitVec.eq_of_toNat_eq (by
      have h0 : j.toNat ≠ 0 := fun h => ‹j ≠ 0#32› (BitVec.eq_of_toNat_eq h)
      have h1 : j.toNat ≠ 1 := fun h => ‹j ≠ 1#32› (BitVec.eq_of_toNat_eq h)
      have h2 : j.toNat ≠ 2 := fun h => ‹j ≠ 2#32› (BitVec.eq_of_toNat_eq h)
      have h3 : j.toNat ≠ 3 := fun h => ‹j ≠ 3#32› (BitVec.eq_of_toNat_eq h)
      have h4 : j.toNat ≠ 4 := fun h => ‹j ≠ 4#32› (BitVec.eq_of_toNat_eq h)
      change j.toNat = 5; omega)
    subst hj5; exact hQ
theorem ar_dzero_wp (Γ : LeanQbe.T.Env) :
    ∀ xs m Q X, arDzeroSpec xs m Q X → Func.wp Γ ar_dzero_body xs m Q X := by
  rintro ⟨dPtr, ⟨⟩⟩ m Q X ⟨d0, R, hlen0, hm, hQ⟩
  c0_hsteps_nogrp
  refine c0_while_state (α := Nat × List (BitVec 64)) (fun p => (BitVec.ofNat 32 p.1, ()))
    (fun p => 16 - p.1) (fun p ml => p.1 ≤ 16 ∧ p.2.length = d0.length ∧ p.2.drop 16 = d0.drop 16 ∧
      (∀ k < p.1, p.2.getD k 0#64 = 0#64) ∧ (array64 dPtr p.2 ⋆ R) ml)
    (fun J hJ => by
      c0_hsteps
      exact hJ (0, d0) m ⟨Nat.zero_le 16, rfl, rfl, fun _ hk => absurd hk (Nat.not_lt_zero _), hm⟩)
    (fun J ⟨idx, d⟩ ml ⟨hle, hlen, hdrop, hzero, hml⟩ ih => by
      dsimp only at hle hlen hdrop hzero hml ih ⊢
      c0_hsteps_nogrp
      · have hlt : idx < 16 := by rw [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)] at hc; exact hc
        have hidx : (BitVec.ofNat 32 idx).toNat < d.length := by
          rw [ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega
        c0_hsteps_nogrp
        simp only [bv64_sw_toNat, ArrayCursorInv.toNat_ofNat_lt (by omega : idx < 2 ^ 32)] at *
        have hzero' : ∀ k < idx + 1, (d.set idx 0#64).getD k 0#64 = 0#64 := fun k hk => by
          by_cases hki : k = idx
          · subst hki; exact d_getD_set_eq d 0#64 0#64 (by omega)
          · rw [getD_set_ne d 0#64 0#64 hki]; exact hzero k (by omega)
        rw [ArrayCursorInv.ofNat_add_one]
        exact ih (idx + 1, d.set idx 0#64) _ (by omega)
          ⟨by omega, by simp [hlen], by rw [List.drop_set_of_lt (by omega), hdrop], hzero',
            by dsimp only; c0_frame⟩
      · have heq : idx = 16 := by
          rw [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)] at hc
          simp only [BitVec.reduceToNat] at hc; omega
        subst heq; c0_hsteps
        exact hQ d ml hlen hdrop hzero (fun σ4 => denseEval64_zero σ4 d hzero) hml)
theorem ar_dlit_wp (Γ : LeanQbe.T.Env)
    (hDzero : ∀ xs m Q X, arDzeroSpec xs m Q X → Γ "ar_dzero" [i64] [] xs m Q X) :
    ∀ xs m Q X, arDlitSpec xs m Q X → Func.wp Γ ar_dlit_body xs m Q X := by
  rintro ⟨dPtr, j, neg, ⟨⟩⟩ m Q X ⟨d0, R, hlen0, hj4, hm, hQ⟩
  c0_hsteps_nogrp; dsimp only [Arg.val]; apply wp_call_of_spec; apply hDzero
  refine ⟨d0, R, hlen0, hm, fun d1 m1 hlen1 hdrop1 hz1 _ hm1 => ?_⟩
  dsimp only [Arg.val] at hm1
  have hshl_toNat : ((1 : BitVec 32) <<< (j.toNat % 32)).toNat = 2 ^ j.toNat := by
    rw [BitVec.toNat_shiftLeft, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega : j.toNat < 32), Nat.shiftLeft_eq, Nat.one_mul,
      Nat.mod_eq_of_lt (Nat.lt_trans (two_pow_lt_16 hj4) (by decide))]
  have hshl_lt : ((1 : BitVec 32) <<< (j.toNat % 32)).toNat < d1.length := by
    rw [hshl_toNat]; have := two_pow_lt_16 hj4; omega
  have hjlt_nat : 1 <<< j.toNat < d1.length := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]; have := two_pow_lt_16 hj4; omega
  have h0_lt : 0 < d1.length := by omega
  c0_hsteps
  · have hshl_lt2 : ((1 : BitVec 32) <<< (j.toNat % 32)).toNat < (d1.set 0 1#64).length := by
      rw [List.length_set]; exact hshl_lt
    c0_hsteps
    let d2 := (d1.set 0 1#64).set ((1 : BitVec 32) <<< (j.toNat % 32)).toNat (0#64 - 1#64)
    have hpow_ne0 : 2 ^ j.toNat ≠ 0 := two_pow_ne_zero j.toNat
    have h0_eq : d2.getD 0 0#64 = 1#64 := by
      dsimp only [d2]; rw [getD_set_ne _ 0#64 _ (by rw [hshl_toNat]; exact hpow_ne0.symm),
        d_getD_set_eq d1 0#64 1#64 h0_lt]
    have h1_eq : d2.getD (2 ^ j.toNat) 0#64 = -1#64 := by
      dsimp only [d2]; rw [← hshl_toNat, d_getD_set_eq (d1.set 0 1#64) 0#64 _ hshl_lt2]; decide
    have hrest : ∀ k < 16, k ≠ 0 → k ≠ 2 ^ j.toNat → d2.getD k 0#64 = 0#64 := fun k hk h0 h1 => by
      dsimp only [d2]; rw [getD_set_ne _ 0#64 _ (by rw [hshl_toNat]; exact h1),
        getD_set_ne _ 0#64 _ h0, hz1 k hk]
    exact hQ d2 _ (by simp [d2, hlen1]) (by
      dsimp only [d2]; rw [List.drop_set_of_lt (by rw [hshl_toNat]; exact two_pow_lt_16 hj4),
        List.drop_set_of_lt (by decide), hdrop1])
      (fun σ4 => by
        rw [ite_eq_left (fun h => hc (by simpa using h))]
        exact denseEval64_lit_neg σ4 d2 hj4 h0_eq h1_eq hrest)
      (by c0_frame)
  · c0_hsteps
    let d2 := d1.set ((1 : BitVec 32) <<< (j.toNat % 32)).toNat 1#64
    have h1_eq : d2.getD (2 ^ j.toNat) 0#64 = 1#64 := by
      dsimp only [d2]; rw [← hshl_toNat, d_getD_set_eq d1 0#64 1#64 hshl_lt]
    have hrest : ∀ k < 16, k ≠ 2 ^ j.toNat → d2.getD k 0#64 = 0#64 := fun k hk h1 => by
      dsimp only [d2]; rw [getD_set_ne d1 0#64 1#64 (by rw [hshl_toNat]; exact h1), hz1 k hk]
    exact hQ d2 _ (by simp [d2, hlen1]) (by
      dsimp only [d2]; rw [List.drop_set_of_lt (by rw [hshl_toNat]; exact two_pow_lt_16 hj4),
        hdrop1])
      (fun σ4 => by
        rw [ite_eq_right (fun h => h hc)]; exact denseEval64_lit_pos σ4 d2 hj4 h1_eq hrest)
      (by c0_frame)

theorem ar_daxpy_wp (Γ : LeanQbe.T.Env) :
    ∀ xs m Q X, arDaxpySpec xs m Q X → Func.wp Γ ar_daxpy_body xs m Q X := by
  rintro ⟨py, k, px, ⟨⟩⟩ m Q X ⟨y0, x, R, hyl0, hxl, hm, hQ⟩
  c0_hsteps_nogrp
  refine c0_while_state (α := Nat × List (BitVec 64)) (fun p => (BitVec.ofNat 32 p.1, ()))
    (fun p => 16 - p.1) (fun p ml => p.1 ≤ 16 ∧ p.2.length = y0.length ∧ p.2.drop 16 = y0.drop 16 ∧
      (∀ q < p.1, p.2.getD q 0#64 = y0.getD q 0#64 + k * x.getD q 0#64) ∧
      (∀ q, p.1 ≤ q → p.2.getD q 0#64 = y0.getD q 0#64) ∧ (∀ σ4 : Nat → Bool, denseEval64 σ4 p.2 =
        denseEval64 σ4 y0 +
          k * (List.range p.1).foldl (fun acc q => acc + denseTerm64 σ4 x q) 0#64) ∧
      (array64 py p.2 ⋆ array64 px x ⋆ R) ml)
    (fun J hJ => by
      c0_hsteps
      exact hJ (0, y0) m ⟨Nat.zero_le 16, rfl, rfl, fun _ hq => absurd hq (Nat.not_lt_zero _),
        fun _ _ => rfl, fun σ4 => by simp, hm⟩)
    (fun J ⟨idx, y⟩ ml ⟨hle, hlen, hdrop, hupd, hrest, heval, hml⟩ ih => by
      dsimp only at hle hlen hdrop hupd hrest heval hml ih ⊢
      c0_hsteps_nogrp
      · have hlt : idx < 16 := by rw [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)] at hc; exact hc
        have hidx_y : (BitVec.ofNat 32 idx).toNat < y.length := by
          rw [ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega
        have hidx_x : (BitVec.ofNat 32 idx).toNat < x.length := by
          rw [ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega
        c0_hsteps_nogrp
        simp only [bv64_sw_toNat, ArrayCursorInv.toNat_ofNat_lt (by omega : idx < 2 ^ 32)] at *
        have hy_idx : y.getD idx 0#64 = y0.getD idx 0#64 := hrest idx (Nat.le_refl _)
        let v := y0.getD idx 0#64 + k * x.getD idx 0#64
        have hupd' : ∀ q < idx + 1,
            (y.set idx v).getD q 0#64 = y0.getD q 0#64 + k * x.getD q 0#64 :=
          fun q hq => by
            by_cases hqi : q = idx
            · subst hqi; exact d_getD_set_eq y 0#64 v (by omega)
            · rw [getD_set_ne y 0#64 v hqi]; exact hupd q (by omega)
        have heval' : ∀ σ4 : Nat → Bool, denseEval64 σ4 (y.set idx v) = denseEval64 σ4 y0 +
            k * (List.range (idx + 1)).foldl (fun acc q => acc + denseTerm64 σ4 x q) 0#64 :=
          fun σ4 => by
            rw [show y.set idx v = y.set idx (y.getD idx 0#64 + k * x.getD idx 0#64) by rw [hy_idx],
              denseEval64_set_add σ4 y hlt (by omega), heval σ4, range_foldl_add_succ]
            unfold denseTerm64; cases denseMono σ4 idx <;> simp [BitVec.mul_add, BitVec.add_assoc]
        rw [ArrayCursorInv.ofNat_add_one]
        refine ih (idx + 1, y.set idx v) _ (by omega) ⟨by omega, by simp [hlen],
          by rw [List.drop_set_of_lt (by omega), hdrop], hupd',
          fun q hq => by rw [getD_set_ne y 0#64 v (by omega)]; exact hrest q (by omega), heval', ?_⟩
        dsimp only [v]
        simp only [← d_getD_eq_getElem y 0#64 (by omega), ← d_getD_eq_getElem x 0#64 (by omega),
          hy_idx] at *
        c0_frame
      · have heq : idx = 16 := by
          rw [Nat.mod_eq_of_lt (by omega : idx < 2 ^ 32)] at hc
          simp only [BitVec.reduceToNat] at hc; omega
        subst heq; c0_hsteps; exact hQ y ml hlen hdrop hupd heval hml)

private theorem bv32_or_lt_16 {i j : Nat} (hi : i < 16) (hj : j < 16) :
    ((BitVec.ofNat 32 i ||| BitVec.ofNat 32 j)).toNat < 16 := by
  rw [BitVec.toNat_or, ArrayCursorInv.toNat_ofNat_lt (by omega),
    ArrayCursorInv.toNat_ofNat_lt (by omega)]
  have H : ∀ a < 16, ∀ b < 16, (a ||| b) < 16 := by decide
  exact H i hi j hj
theorem ar_dmul_wp (Γ : LeanQbe.T.Env)
    (hDzero : ∀ xs m Q X, arDzeroSpec xs m Q X → Γ "ar_dzero" [i64] [] xs m Q X) :
    ∀ xs m Q X, arDmulSpec xs m Q X → Func.wp Γ ar_dmul_body xs m Q X := by
  rintro ⟨pa, pb, pc, ⟨⟩⟩ m Q X ⟨a, b, c0, R, ha_len, hb_len, hc_len, hm, hQ⟩
  c0_hsteps_nogrp; dsimp only [Arg.val]; apply wp_call_of_spec; apply hDzero
  refine ⟨c0, array64 pa a ⋆ array64 pb b ⋆ R, hc_len, (by dsimp only [Arg.val]; c0_frame),
    fun c1 m1 hc1_len hc1_drop _ hc1_eval hm1 => ?_⟩
  dsimp only [Arg.val] at hm1; c0_hsteps_nogrp
  refine c0_while_state (α := Nat × List (BitVec 64)) (fun p => (BitVec.ofNat 32 p.1, ()))
    (fun p => 16 - p.1) (fun p ml => p.1 ≤ 16 ∧ p.2.length = c0.length ∧ p.2.drop 16 = c0.drop 16 ∧
      (∀ σ4 : Nat → Bool, denseEval64 σ4 p.2 =
        (List.range p.1).foldl (fun acc q => acc + denseTerm64 σ4 a q) 0#64 * denseEval64 σ4 b) ∧
      (array64 pa a ⋆ array64 pb b ⋆ array64 pc p.2 ⋆ R) ml)
    (fun J hJ => by
      c0_hsteps
      exact hJ (0, c1) m1 ⟨Nat.zero_le 16, hc1_len, hc1_drop, fun σ4 => by simp [hc1_eval σ4],
        by dsimp only; c0_frame⟩)
    (fun J ⟨i, c⟩ ml ⟨hi_le, hclen, hcdrop, heval, hml⟩ ih => by
      dsimp only at hi_le hclen hcdrop heval hml ih ⊢; c0_hsteps_nogrp
      · have hi : i < 16 := by rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)] at hc; exact hc
        clear hc
        refine wp_join0 (fun ml' => ∃ c' : List (BitVec 64),
          c'.length = c0.length ∧ c'.drop 16 = c0.drop 16 ∧ (∀ σ4 : Nat → Bool, denseEval64 σ4 c' =
            (List.range (i + 1)).foldl (fun acc q => acc + denseTerm64 σ4 a q) 0#64 *
              denseEval64 σ4 b) ∧ (array64 pa a ⋆ array64 pb b ⋆ array64 pc c' ⋆ R) ml')
          (fun _ ml' ⟨c', hc'len, hc'drop, hc'eval, hc'ml⟩ => by
            c0_hsteps; rw [ArrayCursorInv.ofNat_add_one]
            exact ih (i + 1, c') ml' (by omega) ⟨by omega, hc'len, hc'drop, hc'eval, hc'ml⟩)
          (fun J1 hJ1 => by
            have hi_a : (BitVec.ofNat 32 i).toNat < a.length := by
              rw [ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega
            c0_hsteps_nogrp
            · have hnz : a[i]'(by omega) ≠ 0#64 := by
                simp only [Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)] at hc; exact hc
              clear hc; c0_hsteps_nogrp
              refine c0_while_state (α := Nat × List (BitVec 64))
                (fun p => (BitVec.ofNat 32 p.1, ())) (fun p => 16 - p.1)
                (fun p ml' => p.1 ≤ 16 ∧ p.2.length = c0.length ∧ p.2.drop 16 = c0.drop 16 ∧
                  (∀ σ4 : Nat → Bool, denseEval64 σ4 p.2 = denseEval64 σ4 c +
                    denseTerm64 σ4 a i *
                      (List.range p.1).foldl (fun acc q => acc + denseTerm64 σ4 b q) 0#64) ∧
                  (array64 pa a ⋆ array64 pb b ⋆ array64 pc p.2 ⋆ R) ml')
                (fun J2 hJ2 => by
                  c0_hsteps
                  exact hJ2 (0, c) ml ⟨Nat.zero_le 16, hclen, hcdrop, fun σ4 => by simp, hml⟩)
                (fun J2 ⟨j, c_in⟩ ml' ⟨hj_le, hlen', hdrop', heval', hml'⟩ ih2 => by
                  dsimp only at hj_le hlen' hdrop' heval' hml' ih2 ⊢; c0_hsteps_nogrp
                  · have hj : j < 16 := by
                      rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 32)] at hc; exact hc
                    have hj_b : (BitVec.ofNat 32 j).toNat < b.length := by
                      rw [ArrayCursorInv.toNat_ofNat_lt (by omega)]; omega
                    have h_ij_lt :
                        ((BitVec.ofNat 32 i ||| BitVec.ofNat 32 j)).toNat < c_in.length :=
                      by have := bv32_or_lt_16 hi hj; omega
                    c0_hsteps_nogrp
                    let idx := (BitVec.ofNat 32 i ||| BitVec.ofNat 32 j).toNat
                    have hidx_eq : idx = i ||| j := by
                      dsimp only [idx]
                      rw [BitVec.toNat_or, ArrayCursorInv.toNat_ofNat_lt (by omega),
                        ArrayCursorInv.toNat_ofNat_lt (by omega)]
                    have hidx16 : idx < 16 := bv32_or_lt_16 hi hj
                    simp only [bv64_sw_toNat, ArrayCursorInv.toNat_ofNat_lt (by omega : i < 2 ^ 32),
                      ArrayCursorInv.toNat_ofNat_lt (by omega : j < 2 ^ 32)] at *
                    let v := c_in.getD idx 0#64 + a.getD i 0#64 * b.getD j 0#64
                    have heval'' : ∀ σ4 : Nat → Bool, denseEval64 σ4 (c_in.set idx v) =
                        denseEval64 σ4 c + denseTerm64 σ4 a i *
                          (List.range (j + 1)).foldl (fun acc q => acc + denseTerm64 σ4 b q) 0#64 :=
                      fun σ4 => by
                        rw [denseEval64_set_add σ4 c_in hidx16 (by omega), heval' σ4,
                          range_foldl_add_succ, hidx_eq, denseTerm64_or_mul, BitVec.mul_add,
                          BitVec.add_assoc]
                    rw [ArrayCursorInv.ofNat_add_one]
                    refine ih2 (j + 1, c_in.set idx v) _ (by omega)
                      ⟨by omega, by simp [hlen'],
                        by rw [List.drop_set_of_lt hidx16, hdrop'], heval'', ?_⟩
                    dsimp only [v]; simp only [← d_getD_eq_getElem c_in 0#64 h_ij_lt] at hm
                    rw [Std.ExtHashMap.sep_emp] at hm
                    refine sep_cast hm ?_
                    rw [d_getD_eq_getElem a 0#64 (by omega),
                      d_getD_eq_getElem b 0#64 (by omega)]; ac_rfl
                  · have heqj : j = 16 := by
                      rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 32)] at hc
                      simp only [BitVec.reduceToNat] at hc; omega
                    subst heqj; c0_hsteps; refine hJ1 ml' ⟨c_in, hlen', hdrop', fun σ4 => ?_, hml'⟩
                    rw [heval' σ4, heval σ4,
                      range_foldl_add_succ (denseTerm64 σ4 a) i, BitVec.add_mul]
                    rfl)
            · have hz : a[i]'(by omega) = 0#64 := by
                simp only [Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)] at hc; exact hc
              c0_hsteps; refine hJ1 ml ⟨c, hclen, hcdrop, fun σ4 => ?_, hml⟩
              rw [heval σ4, range_foldl_add_succ, BitVec.add_mul]
              have hterm0 : denseTerm64 σ4 a i = 0#64 := by
                unfold denseTerm64; rw [d_getD_eq_getElem a 0#64 (by omega), hz]
                cases denseMono σ4 i <;> rfl
              rw [hterm0, BitVec.zero_mul, BitVec.add_zero])
      · have heqi : i = 16 := by
          rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)] at hc
          simp only [BitVec.reduceToNat] at hc; omega
        subst heqi; c0_hsteps; exact hQ c ml hclen hcdrop heval hml)

/-! ## 4. WP Proof: `ar_dcanon` -/

@[expose] def slice5 (xs : List (BitVec 32)) (off : Nat) : List (BitVec 32) :=
  (List.range 5).map (fun r => xs.getD (off + r) 0#32)
theorem slice5_getD (xs : List (BitVec 32)) (off r : Nat) (hr : r < 5) :
    (slice5 xs off).getD r 0#32 = xs.getD (off + r) 0#32 := by
  simp [slice5, List.getD_eq_getElem?_getD, hr]
theorem slice5_eq_of_eq {xs1 xs2 : List (BitVec 32)} {off1 off2 : Nat}
    (h : ∀ r < 5, xs1.getD (off1 + r) 0#32 = xs2.getD (off2 + r) 0#32) :
    slice5 xs1 off1 = slice5 xs2 off2 := by
  apply List.ext_getElem <;> simp [slice5]; intro r hr; exact h r hr
theorem symListAt_congr_slice5 {xs1 xs2 : List (BitVec 32)} {off1 off2 : Nat}
    (hs : slice5 xs1 off1 = slice5 xs2 off2) (hle : (xs1.getD off1 0#32).toNat ≤ 4) :
    symListAt xs1 off1 = symListAt xs2 off2 := by
  have h0 : xs1.getD off1 0#32 = xs2.getD off2 0#32 := by
    have := congrArg (fun l => l.getD 0 0#32) hs
    rw [slice5_getD _ _ 0 (by decide), slice5_getD _ _ 0 (by decide)] at this; simpa using this
  have h0n : (xs2.getD off2 0#32).toNat = (xs1.getD off1 0#32).toNat :=
    congrArg BitVec.toNat h0.symm
  simp only [symListAt, h0]; apply List.map_congr_left
  intro r hr; rw [List.mem_range] at hr
  have h1 := congrArg (fun l => l.getD (1 + r) 0#32) hs
  rw [slice5_getD _ _ (1 + r) (by omega), slice5_getD _ _ (1 + r) (by omega)] at h1
  rw [Nat.add_assoc, Nat.add_assoc off2, h1]
private theorem symListAt_congr_eq {xs1 xs2 : List (BitVec 32)} {off1 off2 : Nat}
    (h : ∀ r < 5, xs1.getD (off1 + r) 0#32 = xs2.getD (off2 + r) 0#32)
    (hle : (xs2.getD off2 0#32).toNat ≤ 4) :
    symListAt xs1 off1 = symListAt xs2 off2 :=
  (symListAt_congr_slice5 (slice5_eq_of_eq h).symm hle).symm
private theorem symListAt_drop_take5 {xs : List (BitVec 32)} {off : Nat}
    (hoff : off + 5 ≤ xs.length) (hle : (xs.getD off 0#32).toNat ≤ 4) :
    symListAt ((xs.drop off).take 5) 0 = symListAt xs off := by
  refine symListAt_congr_slice5 (slice5_eq_of_eq fun r hr => ?_) ?_
  · rw [List.getD_eq_getElem?_getD, List.getElem?_take, Nat.zero_add,
      ite_eq_left (by omega : r < 5), List.getElem?_drop, List.getElem?_eq_getElem (by omega),
      Option.getD_some, d_getD_eq_getElem xs 0#32 (by omega)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by decide),
      List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem (by omega), Option.getD_some,
      ← d_getD_eq_getElem xs 0#32 (by omega)]
    exact hle
private theorem monoSliceOk_drop_take5 {xs : List (BitVec 32)} {off : Nat}
    (hoff : off + 5 ≤ xs.length) (hle : (xs.getD off 0#32).toNat ≤ 4) :
    MonoSliceOk ((xs.drop off).take 5) 0 ((xs.drop off).take 5).length := by
  have hlen : ((xs.drop off).take 5).length = 5 := by
    rw [List.length_take_of_le]; rw [List.length_drop]; omega
  refine ⟨by rw [hlen]; decide, ?_⟩
  rw [hlen, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by decide),
    List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem (by omega), Option.getD_some,
    ← d_getD_eq_getElem xs 0#32 (by omega), Nat.add_zero]
  omega
private theorem monoSliceOk_of_le4 {xs : List (BitVec 32)} {off bound : Nat}
    (hle : (xs.getD off 0#32).toNat ≤ 4) (hb : off + 5 ≤ bound) : MonoSliceOk xs off bound :=
  ⟨by omega, by omega⟩
private theorem gsyMOff_getD (i : Nat) (hi : i < 16) : (gsyMOff.getD i 0#32).toNat = 5 * i := by
  simp only [gsyMOff, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range, hi, Option.map_some, Option.getD_some]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
private theorem monoValL_eq_denseMono (σ : Nat → Bool) (vs gsy : List (BitVec 32))
    (off mask : Nat) (hmem : ∀ z, z ∈ symListAt gsy off ↔
      ∃ j < 4, mask.testBit j = true ∧ (vs.getD j 0#32).toNat = z) :
    monoValL σ (symListAt gsy off) = denseMono (fun j => σ (vs.getD j 0#32).toNat) mask := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [monoValL_eq_decide, decide_eq_true_eq, denseMono_iff]
  exact ⟨fun h j hj hb => h _ ((hmem _).mpr ⟨j, hj, hb, rfl⟩), fun h z hz => by
    obtain ⟨j, hj, hb, rfl⟩ := (hmem z).mp hz; exact h j hj hb⟩
theorem polyEval_eq_of_perm (nOut : Nat) (σ : Nat → Bool)
    (gsy1 gsy2 : List (BitVec 32)) (gcl1 gch1 gcl2 gch2 : List (BitVec 64)) (n : Nat) (hn : n ≤ 16)
    (hp : ((List.range n).map (fun t =>
        (symListAt gsy1 (5 * t), gcl1.getD t 0#64, gch1.getD t 0#64))).Perm
      ((List.range n).map (fun t =>
        (symListAt gsy2 (5 * t), gcl2.getD t 0#64, gch2.getD t 0#64)))) :
    polyEval nOut σ gsy1 gsyMOff gcl1 gch1 n = polyEval nOut σ gsy2 gsyMOff gcl2 gch2 n := by
  let f : List Nat × BitVec 64 × BitVec 64 → BitVec nOut := fun ⟨syms, lo, hi⟩ =>
    if monoValL σ syms then coeff128 nOut lo hi else 0#nOut
  have h1 : ∀ gsy gcl gch k, k ≤ 16 → polyEval nOut σ gsy gsyMOff gcl gch k =
      ((List.range k).map (fun t =>
        (symListAt gsy (5 * t), gcl.getD t 0#64, gch.getD t 0#64))).foldl
        (fun acc x => acc + f x) 0#nOut := fun gsy gcl gch k hk => by
    simp only [polyEval, polyEvalRange, Nat.zero_add, List.foldl_map]
    induction k with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_cons, List.foldl_nil, ih (by omega)]
      simp only [termEval, gsyMOff_getD m (by omega), f]
  rw [h1 gsy1 gcl1 gch1 n hn, h1 gsy2 gcl2 gch2 n hn]; exact foldl_add_perm f hp
private theorem polyEvalRange_combine_raw (nOut : Nat) (σ : Nat → Bool)
    (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64)) (i m : Nat) (him : i + m ≤ 16)
    (hsym : ∀ d < m, symListAt gsy (5 * (i + d)) = symListAt gsy (5 * i)) :
    polyEvalRange nOut σ gsy gsyMOff gcl gch i m =
      if monoValL σ (symListAt gsy (5 * i)) then
        (List.range m).foldl (fun acc d =>
          acc + coeff128 nOut (gcl.getD (i + d) 0#64) (gch.getD (i + d) 0#64)) 0#nOut
      else 0#nOut := by
  induction m with
  | zero => rw [polyEvalRange_zero, List.range_zero, List.foldl_nil]; cases monoValL σ _ <;> rfl
  | succ m ih =>
    rw [polyEvalRange_succ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ih (by omega) (fun d hd => hsym d (by omega))]
    simp only [termEval, gsyMOff_getD (i + m) (by omega), hsym m (Nat.lt_succ_self m)]
    cases monoValL σ (symListAt gsy (5 * i)) <;> simp
private theorem ar_mcmp_gsy_focus {Γ : LeanQbe.T.Env}
    (hMcmp : ∀ xs m Q X, arMcmpSliceSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    {base : BitVec 64} {gsy : List (BitVec 32)} {offA offB off1 off2 : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (h1 : off1 + 5 ≤ gsy.length) (h2 : off2 + 5 ≤ gsy.length) (hlt : off1 + 5 ≤ off2)
    (hA5 : offA + 5 ≤ gsy.length) (hB5 : offB + 5 ≤ gsy.length)
    (hAle : (gsy.getD offA 0#32).toNat ≤ 4) (hBle : (gsy.getD offB 0#32).toNat ≤ 4)
    (hp1 : offA = off1 ∧ offB = off2 ∨ offA = off2 ∧ offB = off1)
    (hm : (array (t := i32) base gsy ⋆ R) m)
    (hQ : ∀ r : BitVec 32, (r = 0#32 → symListAt gsy offA = symListAt gsy offB) → Q (r, ⟨⟩) m) :
    Γ "ar_mcmp" [i64, i64] [i32]
      (base + BitVec.ofNat 64 (4 * offA), base + BitVec.ofNat 64 (4 * offB), ⟨⟩) m Q X := by
  apply hMcmp; have hm1 := hm; rw [array_slice_focus (t := i32) base gsy h1] at hm1
  have hrem : (off2 - (off1 + 5)) + 5 ≤ (gsy.drop (off1 + 5)).length := by
    rw [List.length_drop]; omega
  rw [array_slice_focus (t := i32) _ (gsy.drop (off1 + 5)) hrem] at hm1
  have hadr : base + BitVec.ofNat 64 (4 * (off1 + 5)) +
      BitVec.ofNat 64 (4 * (off2 - (off1 + 5))) = base + BitVec.ofNat 64 (4 * off2) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hsl : ((gsy.drop (off1 + 5)).drop (off2 - (off1 + 5))).take 5 = (gsy.drop off2).take 5 := by
    rw [List.drop_drop]; congr 1; congr 1; omega
  rw [show (i32 : Ty).bytes = 4 from by decide, hadr, hsl] at hm1
  refine ⟨(gsy.drop offA).take 5, (gsy.drop offB).take 5,
    (array (t := i32) base (gsy.take off1) ⋆ array (t := i32)
      (base + BitVec.ofNat 64 (4 * (off1 + 5))) ((gsy.drop (off1 + 5)).take (off2 - (off1 + 5))) ⋆
      array (t := i32) (base + BitVec.ofNat 64 (4 * (off1 + 5)) +
        BitVec.ofNat 64 (4 * ((off2 - (off1 + 5)) + 5)))
        ((gsy.drop (off1 + 5)).drop ((off2 - (off1 + 5)) + 5)) ⋆ R),
    monoSliceOk_drop_take5 hA5 hAle, monoSliceOk_drop_take5 hB5 hBle,
    by have hms := (monoSliceOk_drop_take5 hA5 hAle).2
       have htl := List.length_take_le 5 (gsy.drop offA)
       omega, ?_,
    fun r hr => hQ r fun h0 => ?_⟩
  · rcases hp1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact sep_cast hm1 (by ac_rfl)
  · have := hr h0; rwa [symListAt_drop_take5 hA5 hAle, symListAt_drop_take5 hB5 hBle] at this
theorem ar_mcmp_gsy {Γ : LeanQbe.T.Env}
    (hMcmp : ∀ xs m Q X, arMcmpSliceSpec xs m Q X → Γ "ar_mcmp" [i64, i64] [i32] xs m Q X)
    {base pA pB : BitVec 64} {gsy : List (BitVec 32)} {offA offB : Nat}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]} {X : XPost}
    (hpA : pA = base + BitVec.ofNat 64 (4 * offA)) (hpB : pB = base + BitVec.ofNat 64 (4 * offB))
    (hA5 : offA + 5 ≤ gsy.length) (hB5 : offB + 5 ≤ gsy.length)
    (hdisj : offA + 5 ≤ offB ∨ offB + 5 ≤ offA)
    (hAle : (gsy.getD offA 0#32).toNat ≤ 4) (hBle : (gsy.getD offB 0#32).toNat ≤ 4)
    (hm : (array (t := i32) base gsy ⋆ R) m)
    (hQ : ∀ r : BitVec 32, (r = 0#32 → symListAt gsy offA = symListAt gsy offB) → Q (r, ⟨⟩) m) :
    Γ "ar_mcmp" [i64, i64] [i32] (pA, pB, ⟨⟩) m Q X := by
  subst hpA hpB
  rcases hdisj with hlt | hlt
  · exact ar_mcmp_gsy_focus hMcmp hA5 hB5 hlt hA5 hB5 hAle hBle (Or.inl ⟨rfl, rfl⟩) hm hQ
  · exact ar_mcmp_gsy_focus hMcmp hB5 hA5 hlt hA5 hB5 hAle hBle (Or.inr ⟨rfl, rfl⟩) hm hQ
@[expose] def DcanonTermInv (s : ArCtxState) (gsy : List (BitVec 32)) (n : Nat) : Prop :=
  n ≤ 16 ∧
  (∀ i < n, MonoSliceOk gsy (5 * i) 80 ∧ (gsy.getD (5 * i) 0#32).toNat ≤ 4 ∧
    ∀ sym ∈ symListAt gsy (5 * i), ∃ j < 4, sym = (s.g_vs.getD j 0#32).toNat) ∧
  (∀ i < n, MonoSorted gsy (5 * i))

@[expose] def Copy5Inv (gsy0 gsy : List (BitVec 32)) (dst src k : Nat) : Prop :=
  k ≤ 5 ∧ gsy.length = gsy0.length ∧ (∀ r < k, gsy.getD (dst + r) 0#32 = gsy0.getD (src + r) 0#32) ∧
  (∀ idx, (idx < dst ∨ dst + 5 ≤ idx) → gsy.getD idx 0#32 = gsy0.getD idx 0#32) ∧
  (dst = src → ∀ r, k ≤ r → r < 5 → gsy.getD (dst + r) 0#32 = gsy0.getD (dst + r) 0#32)
theorem copy5Inv_init (gsy0 : List (BitVec 32)) (dst src : Nat) :
    Copy5Inv gsy0 gsy0 dst src 0 :=
  ⟨Nat.zero_le 5, rfl, fun _ hr => absurd hr (Nat.not_lt_zero _),
    fun _ _ => rfl, fun _ _ _ _ => rfl⟩
theorem copy5Inv_step {gsy0 gsy : List (BitVec 32)} {dst src k : Nat}
    (h : Copy5Inv gsy0 gsy dst src k) (hk : k < 5)
    (hd : dst + 5 ≤ gsy.length) (hs : src + 5 ≤ gsy.length)
    (hdisj : dst = src ∨ dst + 5 ≤ src ∨ src + 5 ≤ dst) :
    Copy5Inv gsy0 (gsy.set (dst + k) (gsy.getD (src + k) 0#32)) dst src (k + 1) := by
  rcases h with ⟨_, hlen, hdone, hout, hsame⟩
  have hval : gsy.getD (src + k) 0#32 = gsy0.getD (src + k) 0#32 := by
    rcases hdisj with rfl | hlt | hlt
    · exact hsame rfl k (Nat.le_refl _) hk
    · exact hout (src + k) (Or.inr (by omega))
    · exact hout (src + k) (Or.inl (by omega))
  refine ⟨by omega, by simp [hlen], fun r hr => ?_, fun idx hidx => ?_, fun hds r hr1 hr2 => ?_⟩
  · by_cases hrk : r = k
    · subst hrk; rw [d_getD_set_eq gsy 0#32 _ (by omega), hval]
    · rw [getD_set_ne gsy 0#32 _ (by omega)]; exact hdone r (by omega)
  · rw [getD_set_ne gsy 0#32 _ (by omega)]; exact hout idx hidx
  · rw [getD_set_ne gsy 0#32 _ (by omega)]; exact hsame hds r (by omega) hr2
private theorem copy5Inv_slice5 {gsy0 gsy : List (BitVec 32)} {dst src : Nat}
    (h : Copy5Inv gsy0 gsy dst src 5) : slice5 gsy dst = slice5 gsy0 src :=
  slice5_eq_of_eq h.2.2.1
theorem bv32_shr_and1_ne0 (mask j : Nat) (hm : mask < 16) (hj : j < 4) :
    (((BitVec.ofNat 32 mask >>> BitVec.ofNat 32 j) &&& 1#32) ≠ 0#32) ↔ mask.testBit j = true := by
  have hsh : (BitVec.ofNat 32 mask >>> BitVec.ofNat 32 j).toNat = mask >>> j := by
    rw [bv_c0_toNat_ushiftRight_bv, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : mask < 2 ^ 32), Nat.mod_eq_of_lt (by omega : j < 2 ^ 32),
      Nat.shiftRight_eq_div_pow]
  have hand : ((BitVec.ofNat 32 mask >>> BitVec.ofNat 32 j) &&& 1#32).toNat = (mask >>> j) % 2 := by
    rw [BitVec.toNat_and, hsh, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
  constructor
  · intro hne
    have h1 : ((BitVec.ofNat 32 mask >>> BitVec.ofNat 32 j) &&& 1#32).toNat ≠ 0 :=
      fun h0 => hne (BitVec.eq_of_toNat_eq (by simpa using h0))
    rw [hand, Nat.shiftRight_eq_div_pow] at h1
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, bne_iff_ne]
    rw [Nat.and_comm 1, Nat.and_one_is_mod]; omega
  · intro ht h0; have h0' := congrArg BitVec.toNat h0
    rw [hand, show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.shiftRight_eq_div_pow] at h0'
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, bne_iff_ne] at ht
    rw [Nat.and_comm 1, Nat.and_one_is_mod] at ht; omega
private theorem range_map_swap_perm {α : Type _} (f g : Nat → α) (n j : Nat)
    (hj0 : 0 < j) (hjn : j < n) (hf1 : g (j - 1) = f j) (hf2 : g j = f (j - 1))
    (hother : ∀ t < n, t ≠ j - 1 → t ≠ j → g t = f t) :
    ((List.range n).map g).Perm ((List.range n).map f) := by
  have hsplit : ∀ k, k ≤ n → ∀ h : Nat → α, (List.range n).map h =
        (List.range k).map h ++ (List.range (n - k)).map (fun d => h (k + d)) :=
    fun k hk h => by
      rw [show n = k + (n - k) by omega, List.range_add, List.map_append, List.map_map]
      simp [Function.comp_def]
  have htail : ∀ h : Nat → α, (List.range (n - (j - 1))).map (fun d => h (j - 1 + d)) =
      h (j - 1) :: h j :: (List.range (n - (j + 1))).map (fun d => h (j + 1 + d)) := fun h => by
    rw [show n - (j - 1) = 2 + (n - (j + 1)) by omega, List.range_add, List.map_append]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.cons_append, Nat.add_zero, show j - 1 + 1 = j by omega, List.map_map, Function.comp_def,
      show ∀ x, j - 1 + (2 + x) = j + 1 + x by intro x; omega]
  rw [hsplit (j - 1) (by omega) f, hsplit (j - 1) (by omega) g, htail f, htail g, hf1, hf2]
  have hp1 : (List.range (j - 1)).map g = (List.range (j - 1)).map f :=
    List.map_congr_left fun t ht => hother t (by rw [List.mem_range] at ht; omega)
      (by rw [List.mem_range] at ht; omega) (by rw [List.mem_range] at ht; omega)
  have hp2 : (List.range (n - (j + 1))).map (fun d => g (j + 1 + d)) =
      (List.range (n - (j + 1))).map (fun d => f (j + 1 + d)) :=
    List.map_congr_left fun d hd => hother (j + 1 + d) (by rw [List.mem_range] at hd; omega)
      (by rw [List.mem_range] at hd; omega) (by rw [List.mem_range] at hd; omega)
  rw [hp1, hp2]; exact List.Perm.append_left _ (List.Perm.swap _ _ _)

@[expose] def Phase1MaskInv (s : ArCtxState) (d : List (BitVec 64))
    (gsy0 gsy : List (BitVec 32)) (gcl0 gcl gch0 gch : List (BitVec 64)) (n mask : Nat) : Prop :=
  n ≤ mask ∧ gsy.length = gsy0.length ∧ gcl.length = gcl0.length ∧ gch.length = gch0.length ∧
  DcanonTermInv s gsy n ∧ ∀ σ : Nat → Bool, polyEval s.modW σ gsy gsyMOff gcl gch n =
    (List.range mask).foldl (fun acc msk =>
      acc + if denseMono (fun j => σ (s.g_vs.getD j 0#32).toNat) msk then
        BitVec.ofInt s.modW (d.getD msk 0#64).toInt else 0#(s.modW))
      0#(s.modW)
theorem phase1MaskInv_step_zero {s : ArCtxState} {d : List (BitVec 64)}
    {gsy0 gsy : List (BitVec 32)} {gcl0 gcl gch0 gch : List (BitVec 64)} {n mask : Nat}
    (h : Phase1MaskInv s d gsy0 gsy gcl0 gcl gch0 gch n mask)
    (hz : BitVec.ofInt s.modW (d.getD mask 0#64).toInt = 0#(s.modW)) :
    Phase1MaskInv s d gsy0 gsy gcl0 gcl gch0 gch n (mask + 1) := by
  rcases h with ⟨hn, h1, h2, h3, hinv, hev⟩; refine ⟨by omega, h1, h2, h3, hinv, fun σ => ?_⟩
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hev σ, hz]
  cases denseMono (fun j => σ (s.g_vs.getD j 0#32).toNat) mask <;> simp

@[expose] def Phase1JInv (s : ArCtxState) (gsy0 gsy1 gsy : List (BitVec 32))
    (n mask j len : Nat) : Prop :=
  j ≤ 4 ∧ len ≤ j ∧ gsy.length = gsy0.length ∧
  (∀ idx, (idx < 5 * n + 1 ∨ 5 * n + 5 ≤ idx) → gsy.getD idx 0#32 = gsy1.getD idx 0#32) ∧
  (∀ z, (∃ r < len, (gsy.getD (5 * n + 1 + r) 0#32).toNat = z) ↔
    (∃ b < j, mask.testBit b = true ∧ (s.g_vs.getD b 0#32).toNat = z)) ∧
  ((List.range len).map (fun r => (gsy.getD (5 * n + 1 + r) 0#32).toNat)).Pairwise (· < ·)
theorem phase1JInv_skip {s : ArCtxState} {gsy0 gsy1 gsy : List (BitVec 32)}
    {n mask j len : Nat} (h : Phase1JInv s gsy0 gsy1 gsy n mask j len)
    (hj4 : j < 4) (hnbit : mask.testBit j = false) :
    Phase1JInv s gsy0 gsy1 gsy n mask (j + 1) len := by
  rcases h with ⟨_, hlen, hgl, hout, hmem, hpair⟩
  refine ⟨by omega, by omega, hgl, hout, fun z => ?_, hpair⟩
  rw [hmem z]
  refine ⟨fun ⟨b, hb, hbt, hbz⟩ => ⟨b, by omega, hbt, hbz⟩, fun ⟨b, hb, hbt, hbz⟩ => ?_⟩
  rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hb) with rfl | hblt
  · rw [hnbit] at hbt; cases hbt
  · exact ⟨b, hblt, hbt, hbz⟩
theorem phase1JInv_dup {s : ArCtxState} {gsy0 gsy1 gsy : List (BitVec 32)}
    {n mask j len q : Nat} (h : Phase1JInv s gsy0 gsy1 gsy n mask j len)
    (hj4 : j < 4) (hbit : mask.testBit j = true) (hq1 : 1 ≤ q) (hqlen : q ≤ len)
    (heq : gsy.getD (5 * n + q) 0#32 = s.g_vs.getD j 0#32) :
    Phase1JInv s gsy0 gsy1 gsy n mask (j + 1) len := by
  rcases h with ⟨_, hlen, hgl, hout, hmem, hpair⟩
  refine ⟨by omega, by omega, hgl, hout, fun z => ?_, hpair⟩
  refine ⟨fun ⟨r, hr, hrz⟩ => ?_, fun ⟨b, hb, hbt, hbz⟩ => ?_⟩
  · obtain ⟨b, hb, hbt, hbz⟩ := (hmem z).mp ⟨r, hr, hrz⟩; exact ⟨b, by omega, hbt, hbz⟩
  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hb) with rfl | hblt
    · refine ⟨q - 1, by omega, ?_⟩
      rw [show 5 * n + 1 + (q - 1) = 5 * n + q by omega, heq, hbz]
    · exact (hmem z).mpr ⟨b, hblt, hbt, hbz⟩
theorem phase1MaskInv_step_nonzero {s : ArCtxState} {d : List (BitVec 64)}
    {gsy0 gsy1 gsyJ : List (BitVec 32)} {gcl0 gcl1 gch0 gch1 : List (BitVec 64)}
    {n mask : Nat} {lenV : BitVec 32} {l h : BitVec 64}
    (hm1 : Phase1MaskInv s d gsy0 gsy1 gcl0 gcl1 gch0 gch1 n mask) (hm16 : mask < 16)
    (hj : Phase1JInv s gsy0 gsy1 gsyJ n mask 4 lenV.toNat)
    (h5 : 5 * n + 5 ≤ gsy0.length) (hnl : n < gcl0.length) (hnh : n < gch0.length)
    (hlh : coeff128 s.modW l h = BitVec.ofInt s.modW (d.getD mask 0#64).toInt) :
    Phase1MaskInv s d gsy0 (gsyJ.set (5 * n) lenV) gcl0 (gcl1.set n l) gch0 (gch1.set n h)
      (n + 1) (mask + 1) := by
  rcases hm1 with ⟨hn_le, hgsy1, hgcl1, hgch1, ⟨_, hinv1, hsort1⟩, heval1⟩
  rcases hj with ⟨_, hlen4, hgsyJ, hout, hmem, hpair⟩
  have hlen_eq : ((gsyJ.set (5 * n) lenV).getD (5 * n) 0#32).toNat = lenV.toNat := by
    rw [d_getD_set_eq gsyJ 0#32 lenV (by omega)]
  have hmem_new : ∀ z, z ∈ symListAt (gsyJ.set (5 * n) lenV) (5 * n) ↔
      ∃ b < 4, mask.testBit b = true ∧ (s.g_vs.getD b 0#32).toNat = z := by
    intro z; rw [mem_symListAt_iff, hlen_eq, ← hmem z]
    constructor
    · rintro ⟨r, hr1, hr2, rfl⟩; refine ⟨r - 1, by omega, ?_⟩
      rw [getD_set_ne gsyJ 0#32 lenV (by omega), show 5 * n + 1 + (r - 1) = 5 * n + r by omega]
    · rintro ⟨r, hr, rfl⟩; refine ⟨r + 1, by omega, by omega, ?_⟩
      rw [getD_set_ne gsyJ 0#32 lenV (by omega), show 5 * n + (r + 1) = 5 * n + 1 + r by omega]
  have hterm_old : ∀ i < n, symListAt (gsyJ.set (5 * n) lenV) (5 * i) = symListAt gsy1 (5 * i) :=
    fun i hi => symListAt_congr_eq (fun r hr => by
      rw [getD_set_ne gsyJ 0#32 lenV (by omega), hout (5 * i + r) (Or.inl (by omega))])
      (hinv1 i hi).2.1
  have hsym_new : symListAt (gsyJ.set (5 * n) lenV) (5 * n) =
      (List.range lenV.toNat).map (fun r => (gsyJ.getD (5 * n + 1 + r) 0#32).toNat) := by
    simp only [symListAt, hlen_eq]
    apply List.map_congr_left
    intro r hr
    rw [Nat.add_assoc, getD_set_ne gsyJ 0#32 lenV (by omega)]
  refine ⟨by omega, by simp [hgsyJ], by simp [hgcl1], by simp [hgch1],
    ⟨by omega, fun i hi => ?_, fun i hi => ?_⟩, fun σ => ?_⟩
  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with rfl | hilt
    · refine ⟨monoSliceOk_of_le4 (by omega) (by omega), by omega, fun sym hs => ?_⟩
      obtain ⟨b, hb, _, rfl⟩ := (hmem_new sym).mp hs; exact ⟨b, hb, rfl⟩
    · obtain ⟨_, hle4, hvs⟩ := hinv1 i hilt
      have h0_eq : (gsyJ.set (5 * n) lenV).getD (5 * i) 0#32 = gsy1.getD (5 * i) 0#32 := by
        rw [getD_set_ne gsyJ 0#32 lenV (by omega), hout (5 * i) (Or.inl (by omega))]
      refine ⟨monoSliceOk_of_le4 (by rw [h0_eq]; exact hle4) (by omega),
        by rw [h0_eq]; exact hle4, by rw [hterm_old i hilt]; exact hvs⟩
  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with rfl | hilt
    · dsimp only [MonoSorted]; rw [hsym_new]; exact hpair
    · exact monoSorted_congr (hterm_old i hilt).symm (hsort1 i hilt)
  · rw [polyEval_succ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ← heval1 σ]
    have hp_old : polyEval s.modW σ (gsyJ.set (5 * n) lenV) gsyMOff
        (gcl1.set n l) (gch1.set n h) n = polyEval s.modW σ gsy1 gsyMOff gcl1 gch1 n := by
      refine polyEval_eq_of_perm s.modW σ _ _ _ _ _ _ n (by omega) ?_
      apply List.Perm.of_eq; apply List.map_congr_left; intro t ht; rw [List.mem_range] at ht
      rw [hterm_old t ht, getD_set_ne gcl1 0#64 l (by omega), getD_set_ne gch1 0#64 h (by omega)]
    rw [hp_old]; congr 1
    rw [termEval, gsyMOff_getD n (by omega), d_getD_set_eq gcl1 0#64 l (by omega),
      d_getD_set_eq gch1 0#64 h (by omega),
      monoValL_eq_denseMono σ s.g_vs _ (5 * n) mask hmem_new, hlh]

@[expose] def Phase2IInv (s : ArCtxState) (gsy0 gsy1 gsy : List (BitVec 32))
    (gcl1 gcl gch1 gch : List (BitVec 64)) (n : Nat) : Prop :=
  gsy.length = gsy0.length ∧ gcl.length = gcl1.length ∧ gch.length = gch1.length ∧
  DcanonTermInv s gsy n ∧
  ((List.range n).map fun t => (symListAt gsy (5 * t), gcl.getD t 0#64, gch.getD t 0#64)).Perm
    ((List.range n).map fun t => (symListAt gsy1 (5 * t), gcl1.getD t 0#64, gch1.getD t 0#64))

@[expose] def Phase2JInv (s : ArCtxState) (gsy0 gsy_s gsy : List (BitVec 32))
    (gcl_s gcl gch_s gch : List (BitVec 64)) (n i j : Nat) (tl th : BitVec 64) : Prop :=
  j ≤ i ∧ gsy.length = gsy0.length ∧ gcl.length = gcl_s.length ∧ gch.length = gch_s.length ∧
  (gsy.getD 80 0#32).toNat ≤ 4 ∧
  (∀ sym ∈ symListAt gsy 80, ∃ b < 4, sym = (s.g_vs.getD b 0#32).toNat) ∧ DcanonTermInv s gsy n ∧
  ((List.range n).map fun t =>
    if t = j then (symListAt gsy 80, tl, th)
    else (symListAt gsy (5 * t), gcl.getD t 0#64, gch.getD t 0#64)).Perm
    ((List.range n).map fun t => (symListAt gsy_s (5 * t), gcl_s.getD t 0#64, gch_s.getD t 0#64)) ∧
  MonoSorted gsy 80
theorem phase2_start_j {s : ArCtxState} {gsy0 gsy1 gsy_s gsy' : List (BitVec 32)}
    {gcl1 gcl_s gch1 gch_s : List (BitVec 64)} {n i : Nat} (hi : i < n)
    (hiInv : Phase2IInv s gsy0 gsy1 gsy_s gcl1 gcl_s gch1 gch_s n)
    (hcp : Copy5Inv gsy_s gsy' 80 (5 * i) 5) :
    Phase2JInv s gsy0 gsy_s gsy' gcl_s gcl_s gch_s gch_s n i i
      (gcl_s.getD i 0#64) (gch_s.getD i 0#64) := by
  rcases hiInv with ⟨hgsy, hgcl, hgch, ⟨hn16, hinv, hsort⟩, hperm⟩
  have h80_sym : symListAt gsy' 80 = symListAt gsy_s (5 * i) :=
    symListAt_congr_eq hcp.2.2.1 (hinv i hi).2.1
  have h80_0 : (gsy'.getD 80 0#32).toNat = (gsy_s.getD (5 * i) 0#32).toNat := by
    rw [← Nat.add_zero 80, hcp.2.2.1 0 (by decide), Nat.add_zero]
  have hout_sym : ∀ t < n, symListAt gsy' (5 * t) = symListAt gsy_s (5 * t) := fun t ht =>
    symListAt_congr_eq (fun r hr => hcp.2.2.2.1 (5 * t + r) (Or.inl (by omega))) (hinv t ht).2.1
  refine ⟨Nat.le_refl i, by rw [hcp.2.1, hgsy], rfl, rfl, by rw [h80_0]; exact (hinv i hi).2.1,
    by rw [h80_sym]; exact (hinv i hi).2.2,
    ⟨hn16, fun t ht => ?_, fun t ht => monoSorted_congr (hout_sym t ht).symm (hsort t ht)⟩,
    ?_, monoSorted_congr h80_sym.symm (hsort i hi)⟩
  · have h0 : gsy'.getD (5 * t) 0#32 = gsy_s.getD (5 * t) 0#32 :=
      hcp.2.2.2.1 (5 * t) (Or.inl (by omega))
    exact ⟨monoSliceOk_of_le4 (by rw [h0]; exact (hinv t ht).2.1) (by omega),
      by rw [h0]; exact (hinv t ht).2.1, by rw [hout_sym t ht]; exact (hinv t ht).2.2⟩
  · apply List.Perm.of_eq; apply List.map_congr_left
    intro t ht; rw [List.mem_range] at ht
    by_cases hti : t = i
    · subst hti; simp [h80_sym]
    · simp [hti, hout_sym t ht]
theorem phase2_step_j {s : ArCtxState} {gsy0 gsy_s gsy gsy' : List (BitVec 32)}
    {gcl_s gcl gch_s gch : List (BitVec 64)} {n i j : Nat} {tl th : BitVec 64}
    (hj0 : 0 < j) (hj : Phase2JInv s gsy0 gsy_s gsy gcl_s gcl gch_s gch n i j tl th)
    (_hin : i < n) (hcp : Copy5Inv gsy gsy' (5 * j) (5 * (j - 1)) 5)
    (hjl : j < gcl.length) (hjh : j < gch.length) :
    Phase2JInv s gsy0 gsy_s gsy' gcl_s (gcl.set j (gcl.getD (j - 1) 0#64)) gch_s
      (gch.set j (gch.getD (j - 1) 0#64)) n i (j - 1) tl th := by
  rcases hj with ⟨hji, hgsy, hgcl, hgch, h80le, h80vs, ⟨hn16, hinv, hsort⟩, hperm, h80s⟩
  have h80_sym : symListAt gsy' 80 = symListAt gsy 80 :=
    symListAt_congr_eq (fun r hr => hcp.2.2.2.1 (80 + r) (Or.inr (by omega))) h80le
  have h80_0 : gsy'.getD 80 0#32 = gsy.getD 80 0#32 := hcp.2.2.2.1 80 (Or.inr (by omega))
  have hslot_j : symListAt gsy' (5 * j) = symListAt gsy (5 * (j - 1)) :=
    symListAt_congr_eq hcp.2.2.1 (hinv (j - 1) (by omega)).2.1
  have hslot_o : ∀ t < n, t ≠ j → symListAt gsy' (5 * t) = symListAt gsy (5 * t) := fun t ht htj =>
    symListAt_congr_eq (fun r hr => by
      rcases show 5 * t + 5 ≤ 5 * j ∨ 5 * j + 5 ≤ 5 * t by omega with hlt | hlt
      · exact hcp.2.2.2.1 (5 * t + r) (Or.inl (by omega))
      · exact hcp.2.2.2.1 (5 * t + r) (Or.inr (by omega))) (hinv t ht).2.1
  refine ⟨by omega, by rw [hcp.2.1, hgsy], by simp [hgcl], by simp [hgch],
    by rw [h80_0]; exact h80le, by rw [h80_sym]; exact h80vs,
    ⟨hn16, fun t ht => ?_, fun t ht => ?_⟩,
    ?_, monoSorted_congr h80_sym.symm h80s⟩
  · by_cases htj : t = j
    · subst htj
      have h0 : (gsy'.getD (5 * t) 0#32).toNat ≤ 4 := by
        rw [← Nat.add_zero (5 * t), hcp.2.2.1 0 (by decide), Nat.add_zero]
        exact (hinv (t - 1) (by omega)).2.1
      exact ⟨monoSliceOk_of_le4 h0 (by omega), h0,
        by rw [hslot_j]; exact (hinv (t - 1) (by omega)).2.2⟩
    · have h0 : (gsy'.getD (5 * t) 0#32).toNat ≤ 4 := by
        rcases show 5 * t + 5 ≤ 5 * j ∨ 5 * j + 5 ≤ 5 * t by omega with hlt | hlt
        · rw [hcp.2.2.2.1 (5 * t) (Or.inl (by omega))]; exact (hinv t ht).2.1
        · rw [hcp.2.2.2.1 (5 * t) (Or.inr (by omega))]; exact (hinv t ht).2.1
      exact ⟨monoSliceOk_of_le4 h0 (by omega), h0, by rw [hslot_o t ht htj]; exact (hinv t ht).2.2⟩
  · by_cases htj : t = j
    · subst htj; exact monoSorted_congr hslot_j.symm (hsort (t - 1) (by omega))
    · exact monoSorted_congr (hslot_o t ht htj).symm (hsort t ht)
  · refine List.Perm.trans ?_ hperm
    refine range_map_swap_perm _ _ n j hj0 (by omega) ?_ ?_ (fun t ht h1 h2 => ?_)
    · rw [ite_eq_left rfl, ite_eq_left rfl, h80_sym]
    · rw [ite_eq_right (by omega : j ≠ j - 1), ite_eq_right (by omega : j - 1 ≠ j), hslot_j,
        d_getD_set_eq gcl 0#64 _ hjl, d_getD_set_eq gch 0#64 _ hjh]
    · rw [ite_eq_right h1, ite_eq_right h2, hslot_o t ht h2,
        getD_set_ne gcl 0#64 _ h2, getD_set_ne gch 0#64 _ h2]

theorem phase2_finish_j {s : ArCtxState} {gsy0 gsy1 gsy_s gsy gsy' : List (BitVec 32)}
    {gcl1 gcl_s gcl gch1 gch_s gch : List (BitVec 64)} {n i j : Nat} {tl th : BitVec 64}
    (hiInv : Phase2IInv s gsy0 gsy1 gsy_s gcl1 gcl_s gch1 gch_s n)
    (hj : Phase2JInv s gsy0 gsy_s gsy gcl_s gcl gch_s gch n i j tl th)
    (_hin : i < n) (hcp : Copy5Inv gsy gsy' (5 * j) 80 5)
    (hjl : j < gcl.length) (hjh : j < gch.length) :
    Phase2IInv s gsy0 gsy1 gsy' gcl1 (gcl.set j tl) gch1 (gch.set j th) n := by
  rcases hj with ⟨hji, hgsy, hgcl, hgch, h80le, h80vs, ⟨hn16, hinv, hsort⟩, hperm, h80s⟩
  have hslot_j : symListAt gsy' (5 * j) = symListAt gsy 80 := symListAt_congr_eq hcp.2.2.1 h80le
  have hslot_o : ∀ t < n, t ≠ j → symListAt gsy' (5 * t) = symListAt gsy (5 * t) := fun t ht htj =>
    symListAt_congr_eq (fun r hr => by
      rcases show 5 * t + 5 ≤ 5 * j ∨ 5 * j + 5 ≤ 5 * t by omega with hlt | hlt
      · exact hcp.2.2.2.1 (5 * t + r) (Or.inl (by omega))
      · exact hcp.2.2.2.1 (5 * t + r) (Or.inr (by omega))) (hinv t ht).2.1
  refine ⟨by rw [hcp.2.1, hgsy], by rw [List.length_set, hgcl, hiInv.2.1],
    by rw [List.length_set, hgch, hiInv.2.2.1], ⟨hn16, fun t ht => ?_, fun t ht => ?_⟩,
    List.Perm.trans ?_ (List.Perm.trans hperm hiInv.2.2.2.2)⟩
  · by_cases htj : t = j
    · subst htj
      have h0 : (gsy'.getD (5 * t) 0#32).toNat ≤ 4 := by
        rw [← Nat.add_zero (5 * t), hcp.2.2.1 0 (by decide), Nat.add_zero]; exact h80le
      exact ⟨monoSliceOk_of_le4 h0 (by omega), h0, by rw [hslot_j]; exact h80vs⟩
    · have h0 : (gsy'.getD (5 * t) 0#32).toNat ≤ 4 := by
        rcases show 5 * t + 5 ≤ 5 * j ∨ 5 * j + 5 ≤ 5 * t by omega with hlt | hlt
        · rw [hcp.2.2.2.1 (5 * t) (Or.inl (by omega))]; exact (hinv t ht).2.1
        · rw [hcp.2.2.2.1 (5 * t) (Or.inr (by omega))]; exact (hinv t ht).2.1
      exact ⟨monoSliceOk_of_le4 h0 (by omega), h0, by rw [hslot_o t ht htj]; exact (hinv t ht).2.2⟩
  · by_cases htj : t = j
    · subst htj; exact monoSorted_congr hslot_j.symm h80s
    · exact monoSorted_congr (hslot_o t ht htj).symm (hsort t ht)
  · apply List.Perm.of_eq; apply List.map_congr_left
    intro t ht; rw [List.mem_range] at ht
    by_cases htj : t = j
    · subst htj; rw [ite_eq_left rfl, hslot_j, d_getD_set_eq gcl 0#64 _ hjl,
        d_getD_set_eq gch 0#64 _ hjh]
    · rw [ite_eq_right htj, hslot_o t ht htj, getD_set_ne gcl 0#64 _ htj,
        getD_set_ne gch 0#64 _ htj]

@[expose] def Phase3IInv (s : ArCtxState) (gsy0 gsy2 gsy : List (BitVec 32))
    (gcl2 gcl gch2 gch : List (BitVec 64)) (n k i : Nat) : Prop :=
  k ≤ i ∧ i ≤ n ∧ gsy.length = gsy0.length ∧ gcl.length = gcl2.length ∧ gch.length = gch2.length ∧
  DcanonTermInv s gsy k ∧ (∀ t, i ≤ t → t < n → slice5 gsy (5 * t) = slice5 gsy2 (5 * t) ∧
    gcl.getD t 0#64 = gcl2.getD t 0#64 ∧ gch.getD t 0#64 = gch2.getD t 0#64) ∧
  ∀ σ : Nat → Bool, polyEval s.modW σ gsy gsyMOff gcl gch k +
    polyEvalRange s.modW σ gsy2 gsyMOff gcl2 gch2 i (n - i) =
    polyEval s.modW σ gsy2 gsyMOff gcl2 gch2 n
theorem phase3_step_zero {s : ArCtxState} {gsy0 gsy2 gsy : List (BitVec 32)}
    {gcl2 gcl gch2 gch : List (BitVec 64)} {n k i j : Nat}
    (hp : Phase3IInv s gsy0 gsy2 gsy gcl2 gcl gch2 gch n k i)
    (hinv2 : DcanonTermInv s gsy2 n) (hij : i < j) (hjn : j ≤ n)
    (hsym : ∀ d < j - i, symListAt gsy2 (5 * (i + d)) = symListAt gsy2 (5 * i))
    (hlh0 : (List.range (j - i)).foldl (fun acc d =>
      acc + coeff128 s.modW (gcl2.getD (i + d) 0#64) (gch2.getD (i + d) 0#64))
      0#(s.modW) = 0#(s.modW)) :
    Phase3IInv s gsy0 gsy2 gsy gcl2 gcl gch2 gch n k j := by
  rcases hp with ⟨hki, _, hgsy, hgcl, hgch, hinvk, htail, heval⟩
  refine ⟨by omega, hjn, hgsy, hgcl, hgch, hinvk, fun t ht1 ht2 => htail t (by omega) ht2,
    fun σ => ?_⟩
  rw [← heval σ]; congr 1
  rw [show n - i = (j - i) + (n - j) by omega, polyEvalRange_add, show i + (j - i) = j by omega]
  have hzero :
      polyEvalRange s.modW σ gsy2 gsyMOff gcl2 gch2 i (j - i) = 0#(s.modW) := by
    have := hinv2.1
    rw [polyEvalRange_combine_raw s.modW σ gsy2 gcl2 gch2 i (j - i) (by omega) hsym, hlh0]
    cases monoValL σ (symListAt gsy2 (5 * i)) <;> rfl
  rw [hzero, BitVec.zero_add]
theorem phase3_step_nonzero {s : ArCtxState} {gsy0 gsy2 gsy gsy' : List (BitVec 32)}
    {gcl2 gcl gch2 gch : List (BitVec 64)} {n k i j : Nat} {l h : BitVec 64}
    (hp : Phase3IInv s gsy0 gsy2 gsy gcl2 gcl gch2 gch n k i)
    (hinv2 : DcanonTermInv s gsy2 n) (hij : i < j) (hjn : j ≤ n)
    (hcp : Copy5Inv gsy gsy' (5 * k) (5 * i) 5) (hkl : k < gcl.length) (hkh : k < gch.length)
    (hsym : ∀ d < j - i, symListAt gsy2 (5 * (i + d)) = symListAt gsy2 (5 * i))
    (hlh : coeff128 s.modW l h = (List.range (j - i)).foldl (fun acc d =>
      acc + coeff128 s.modW (gcl2.getD (i + d) 0#64) (gch2.getD (i + d) 0#64))
      0#(s.modW)) :
    Phase3IInv s gsy0 gsy2 gsy' gcl2 (gcl.set k l) gch2 (gch.set k h) n (k + 1) j := by
  rcases hp with ⟨hki, _, hgsy, hgcl, hgch, ⟨_, hinvk, hsortk⟩, htail, heval⟩
  have hn16 := hinv2.1
  have h0i : gsy.getD (5 * i) 0#32 = gsy2.getD (5 * i) 0#32 := by
    have := congrArg (fun x => x.getD 0 0#32) (htail i (Nat.le_refl i) (by omega)).1
    rw [slice5_getD _ _ 0 (by decide), slice5_getD _ _ 0 (by decide)] at this
    simpa only [Nat.add_zero] using this
  have hslot_k : symListAt gsy' (5 * k) = symListAt gsy2 (5 * i) := by
    refine symListAt_congr_slice5
      ((copy5Inv_slice5 hcp).trans (htail i (Nat.le_refl i) (by omega)).1) ?_
    rw [← Nat.add_zero (5 * k), hcp.2.2.1 0 (by decide), Nat.add_zero, h0i]
    exact (hinv2.2.1 i (by omega)).2.1
  have hslot_old : ∀ t < k, symListAt gsy' (5 * t) = symListAt gsy (5 * t) := fun t ht =>
    symListAt_congr_eq (fun r hr => hcp.2.2.2.1 (5 * t + r) (Or.inl (by omega))) (hinvk t ht).2.1
  refine ⟨by omega, hjn, by rw [hcp.2.1, hgsy], by simp [hgcl], by simp [hgch],
    ⟨by omega, fun t ht => ?_, fun t ht => ?_⟩, fun t ht1 ht2 => ?_, fun σ => ?_⟩
  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp ht) with rfl | hlt
    · have h0 : (gsy'.getD (5 * t) 0#32).toNat ≤ 4 := by
        rw [← Nat.add_zero (5 * t), hcp.2.2.1 0 (by decide), Nat.add_zero, h0i]
        exact (hinv2.2.1 i (by omega)).2.1
      exact ⟨monoSliceOk_of_le4 h0 (by omega), h0,
        by rw [hslot_k]; exact (hinv2.2.1 i (by omega)).2.2⟩
    · have h0 : (gsy'.getD (5 * t) 0#32).toNat ≤ 4 := by
        rw [hcp.2.2.2.1 (5 * t) (Or.inl (by omega))]; exact (hinvk t hlt).2.1
      exact ⟨monoSliceOk_of_le4 h0 (by omega), h0, by rw [hslot_old t hlt]; exact (hinvk t hlt).2.2⟩
  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp ht) with rfl | hlt
    · exact monoSorted_congr hslot_k.symm (hinv2.2.2 i (by omega))
    · exact monoSorted_congr (hslot_old t hlt).symm (hsortk t hlt)
  · refine ⟨slice5_eq_of_eq fun r hr => ?_,
      by rw [getD_set_ne gcl 0#64 _ (by omega)]; exact (htail t (by omega) ht2).2.1,
      by rw [getD_set_ne gch 0#64 _ (by omega)]; exact (htail t (by omega) ht2).2.2⟩
    rw [hcp.2.2.2.1 (5 * t + r) (Or.inr (by omega))]
    have := congrArg (fun x => x.getD r 0#32) (htail t (by omega) ht2).1
    rwa [slice5_getD _ _ r hr, slice5_getD _ _ r hr] at this
  · rw [← heval σ, polyEval_succ]
    have hp_old : polyEval s.modW σ gsy' gsyMOff (gcl.set k l) (gch.set k h) k =
        polyEval s.modW σ gsy gsyMOff gcl gch k := by
      refine polyEval_eq_of_perm s.modW σ _ _ _ _ _ _ k (by omega) ?_
      apply List.Perm.of_eq; apply List.map_congr_left; intro t ht; rw [List.mem_range] at ht
      rw [hslot_old t ht, getD_set_ne gcl 0#64 l (by omega), getD_set_ne gch 0#64 h (by omega)]
    rw [hp_old, show n - i = (j - i) + (n - j) by omega, polyEvalRange_add,
      show i + (j - i) = j by omega, BitVec.add_assoc]
    congr 1; congr 1
    rw [termEval, gsyMOff_getD k (by omega), hslot_k, d_getD_set_eq gcl 0#64 l hkl,
      d_getD_set_eq gch 0#64 h hkh, polyEvalRange_combine_raw s.modW σ gsy2 gcl2 gch2 i
      (j - i) (by omega) hsym, hlh]

@[expose] def Phase1KInv (_s : ArCtxState) (gsy0 gsy1 gsy_j gsy : List (BitVec 32))
    (n q len k : Nat) : Prop :=
  q ≤ k ∧ k ≤ len ∧ gsy.length = gsy0.length ∧
  (∀ idx, (idx < 5 * n + 1 ∨ 5 * n + 5 ≤ idx) → gsy.getD idx 0#32 = gsy1.getD idx 0#32) ∧
  (∀ r, 1 ≤ r → r ≤ k → gsy.getD (5 * n + r) 0#32 = gsy_j.getD (5 * n + r) 0#32) ∧
  (∀ r, k + 2 ≤ r → r ≤ len + 1 → gsy.getD (5 * n + r) 0#32 = gsy_j.getD (5 * n + (r - 1)) 0#32)
theorem phase1KInv_step {_s : ArCtxState} {gsy0 gsy1 gsy_j gsy : List (BitVec 32)}
    {n q len k : Nat} (hk : Phase1KInv _s gsy0 gsy1 gsy_j gsy n q len k)
    (hgt : q < k) (_hkl : len < 4) (h5 : 5 * n + 5 ≤ gsy0.length) :
    Phase1KInv _s gsy0 gsy1 gsy_j (gsy.set (5 * n + k + 1) (gsy.getD (5 * n + k) 0#32))
      n q len (k - 1) := by
  rcases hk with ⟨hqk, hkle, hgl, hout, hle, hge⟩
  refine ⟨by omega, by omega, by simp [hgl], fun idx hidx => ?_, fun r hr1 hr2 => ?_,
    fun r hr1 hr2 => ?_⟩
  · rw [getD_set_ne gsy 0#32 _ (by omega)]; exact hout idx hidx
  · rw [getD_set_ne gsy 0#32 _ (by omega)]; exact hle r hr1 (by omega)
  · by_cases heq : r = k + 1
    · subst heq
      rw [show 5 * n + (k + 1) = 5 * n + k + 1 by omega, d_getD_set_eq gsy 0#32 _ (by omega),
        show k + 1 - 1 = k by omega]
      exact hle k (by omega) (Nat.le_refl k)
    · rw [getD_set_ne gsy 0#32 _ (by omega)]; exact hge r (by omega) hr2
private theorem phase1_shift_mem {gsy0 gsy : List (BitVec 32)} {off len q : Nat} {x : BitVec 32}
    (hq : q ≤ len) (hle : ∀ r, 1 ≤ r → r ≤ q → gsy.getD (off + r) 0#32 = gsy0.getD (off + r) 0#32)
    (hge : ∀ r, q + 2 ≤ r → r ≤ len + 1 → gsy.getD (off + r) 0#32 = gsy0.getD (off + (r - 1)) 0#32)
    (hq1 : gsy.getD (off + q + 1) 0#32 = x) :
    ∀ z, (∃ r < len + 1, (gsy.getD (off + 1 + r) 0#32).toNat = z) ↔
      (z = x.toNat ∨ ∃ r < len, (gsy0.getD (off + 1 + r) 0#32).toNat = z) := by
  intro z; constructor
  · rintro ⟨r, hr, rfl⟩
    by_cases hlt : r < q
    · right; exact ⟨r, by omega, by
        rw [show off + 1 + r = off + (1 + r) by omega, hle (1 + r) (by omega) (by omega)]⟩
    · by_cases heq : r = q
      · left; subst heq; rw [show off + 1 + r = off + r + 1 by omega, hq1]
      · right; refine ⟨r - 1, by omega, ?_⟩
        rw [show off + 1 + r = off + (1 + r) by omega, hge (1 + r) (by omega) (by omega)]
        congr 2; omega
  · rintro (rfl | ⟨r, hr, rfl⟩)
    · exact ⟨q, by omega, by rw [show off + 1 + q = off + q + 1 by omega, hq1]⟩
    · by_cases hlt : r < q
      · exact ⟨r, by omega, by
          rw [show off + 1 + r = off + (1 + r) by omega, hle (1 + r) (by omega) (by omega)]⟩
      · refine ⟨r + 1, by omega, ?_⟩
        rw [show off + 1 + (r + 1) = off + (r + 2) by omega, hge (r + 2) (by omega) (by omega)]
        congr 2; omega
theorem phase1KInv_done {s : ArCtxState} {gsy0 gsy1 gsy_j gsy : List (BitVec 32)}
    {n mask j q len : Nat} (hj : Phase1JInv s gsy0 gsy1 gsy_j n mask j len)
    (hk : Phase1KInv s gsy0 gsy1 gsy_j gsy n q len q)
    (hj4 : j < 4) (hbit : mask.testBit j = true) (h5 : 5 * n + 5 ≤ gsy0.length)
    (hq0 : q = 0 ∨ (gsy_j.getD (5 * n + q) 0#32).toNat < (s.g_vs.getD j 0#32).toNat)
    (hqlen : ∀ r, q + 1 ≤ r → r ≤ len →
      (s.g_vs.getD j 0#32).toNat < (gsy_j.getD (5 * n + r) 0#32).toNat) :
    Phase1JInv s gsy0 gsy1 (gsy.set (5 * n + q + 1) (s.g_vs.getD j 0#32))
      n mask (j + 1) (len + 1) := by
  rcases hj with ⟨_, hlj, _, _, hmem, hpair⟩
  rcases hk with ⟨_, hql, hgl, hout, hle, hge⟩; let x := s.g_vs.getD j 0#32
  have hdst : 5 * n + q + 1 < gsy.length := by omega
  have hpm := phase1_shift_mem (gsy0 := gsy_j) (gsy := gsy.set (5 * n + q + 1) x) hql
    (fun r hr1 hr2 => by
      change (gsy.set (5 * n + q + 1) x).getD (5 * n + r) 0#32 = _
      rw [getD_set_ne gsy 0#32 x (by omega)]; exact hle r hr1 hr2)
    (fun r hr1 hr2 => by
      change (gsy.set (5 * n + q + 1) x).getD (5 * n + r) 0#32 = _
      rw [getD_set_ne gsy 0#32 x (by omega)]; exact hge r (by omega) hr2)
    (d_getD_set_eq gsy 0#32 x hdst)
  have hpair_get : ∀ a b, a < b → b < len →
      (gsy_j.getD (5 * n + 1 + a) 0#32).toNat < (gsy_j.getD (5 * n + 1 + b) 0#32).toNat := by
    rw [List.pairwise_iff_getElem] at hpair
    intro a b hab hb
    have h := hpair a b (by simp; omega) (by simp; omega) hab
    simp only [List.getElem_map, List.getElem_range] at h; exact h
  have hpair_new :
      ((List.range (len + 1)).map (fun r =>
        ((gsy.set (5 * n + q + 1) x).getD (5 * n + 1 + r) 0#32).toNat)).Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro a b hlenA hlenB hab
    simp only [List.length_map, List.length_range] at hlenA hlenB
    simp only [List.getElem_map, List.getElem_range]
    have hval : ∀ r < len + 1,
        ((gsy.set (5 * n + q + 1) x).getD (5 * n + 1 + r) 0#32).toNat =
          if r < q then (gsy_j.getD (5 * n + 1 + r) 0#32).toNat
          else if r = q then x.toNat
          else (gsy_j.getD (5 * n + r) 0#32).toNat := by
      intro r hr
      by_cases hrq : r < q
      · rw [ite_eq_left hrq, getD_set_ne gsy 0#32 x (by omega)]
        exact congrArg BitVec.toNat (hle (r + 1) (by omega) (by omega) |> fun h => by
          simpa only [Nat.add_assoc, show 1 + r = r + 1 from Nat.add_comm 1 r] using h)
      · by_cases hreq : r = q
        · subst hreq; rw [ite_eq_right hrq, ite_eq_left rfl, show 5 * n + 1 + r = 5 * n + r + 1 by
            omega, d_getD_set_eq gsy 0#32 x hdst]
        · rw [ite_eq_right hrq, ite_eq_right hreq, getD_set_ne gsy 0#32 x (by omega)]
          exact congrArg BitVec.toNat (hge (r + 1) (by omega) (by omega) |> fun h => by
            simpa only [Nat.add_assoc, show 1 + r = r + 1 from Nat.add_comm 1 r,
              Nat.add_sub_cancel] using h)
    rw [hval a (by omega), hval b hlenB]
    have hax : ∀ t < q, (gsy_j.getD (5 * n + 1 + t) 0#32).toNat < x.toNat := by
      intro t ht
      have hqpos : 0 < q := by omega
      have hqlt : (gsy_j.getD (5 * n + q) 0#32).toNat < x.toNat := by
        rcases hq0 with rfl | hlt
        · omega
        · exact hlt
      by_cases ht1 : t + 1 = q
      · rw [Nat.add_assoc, show 1 + t = q by omega]; exact hqlt
      · have := hpair_get t (q - 1) (by omega) (by omega)
        rw [show 5 * n + 1 + (q - 1) = 5 * n + q by omega] at this
        exact lt_trans (by simpa only [Nat.add_assoc] using this) hqlt
    by_cases ha : a < q <;> by_cases hb : b < q
    · simp only [ha, hb, ↓reduceIte]; exact hpair_get a b hab (by omega)
    · by_cases hbeq : b = q
      · simp only [ha, hbeq, Nat.lt_irrefl, ↓reduceIte]; exact hax a ha
      · simp only [ha, hb, hbeq, ↓reduceIte]
        exact lt_trans (hax a ha) (hqlen b (by omega) (by omega))
    · exfalso; omega
    · by_cases haeq : a = q
      · subst haeq
        have hbnq : ¬ b = a := by omega
        simp only [Nat.lt_irrefl, ↓reduceIte, hbnq, hb]
        exact hqlen b (by omega) (by omega)
      · have hbnq : ¬ b = q := by omega
        simp only [ha, haeq, hb, hbnq, ↓reduceIte]
        have := hpair_get (a - 1) (b - 1) (by omega) (by omega)
        simpa only [Nat.add_assoc, show 1 + (a - 1) = a by omega,
          show 1 + (b - 1) = b by omega] using this
  refine ⟨by omega, by omega, by simp [hgl],
    fun idx hidx => by rw [getD_set_ne gsy 0#32 x (by omega)]; exact hout idx hidx, fun z => ?_,
    hpair_new⟩
  dsimp only [x] at hpm ⊢; rw [hpm z, hmem z]
  refine ⟨fun h => ?_, fun ⟨b, hb, hbt, hbz⟩ => ?_⟩
  · rcases h with rfl | ⟨b, hb, hbt, hbz⟩
    · exact ⟨j, by omega, hbit, rfl⟩
    · exact ⟨b, by omega, hbt, hbz⟩
  · rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hb) with rfl | hblt
    · exact Or.inl hbz.symm
    · exact Or.inr ⟨b, hblt, hbt, hbz⟩
theorem set_eq_of_eq {α : Type _} {xs : List α} {i j : Nat} {v w : α}
    (hij : i = j) (hvw : v = w) : xs.set i v = xs.set j w := by subst hij hvw; rfl
theorem getElem_eq_getD {α : Type _} {xs : List α} {i j : Nat} (d : α)
    (hi : i < xs.length) (hij : i = j) : xs[i]'hi = xs.getD j d := by
  subst hij; exact (d_getD_eq_getElem xs d hi).symm
theorem bv64_sw_mul5_add_eq {x k : BitVec 32} (hx : x.toNat < 16) (hk : k.toNat < 5) :
    (BitVec.setWidth 64 (5 * x + k)).toNat = 5 * x.toNat + k.toNat := by
  rw [bv64_sw_toNat, BitVec.toNat_add, BitVec.toNat_mul, show (5 : BitVec 32).toNat = 5 from rfl,
    Nat.mod_eq_of_lt (by omega : 5 * x.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 5 * x.toNat + k.toNat < 2 ^ 32)]
theorem bv64_sw_mul5_add_lt {x k : BitVec 32} {len : Nat}
    (hx : x.toNat < 16) (hk : k.toNat < 5) (hlen : 85 ≤ len) :
    (BitVec.setWidth 64 (5 * x + k)).toNat < len := by rw [bv64_sw_mul5_add_eq hx hk]; omega


/-! ## 5A. Truth-Table Bitmask & Memory-Packing Helpers -/

abbrev padU32 (a : BitVec 64) (n : Nat) : Mem 64 → Prop :=
  region (a + BitVec.ofNat 64 (4 * n)) (align8 (4 * n) - 4 * n)
theorem bv32_ushr1 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
theorem bv32_and1_ne (x : BitVec 32) : (x &&& 1 ≠ 0#32) ↔ x.toNat % 2 = 1 := by
  rw [ne_eq, ← BitVec.toNat_inj, BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
    show (0#32).toNat = 0 from rfl, Nat.and_one_is_mod]
  omega
theorem bv64_not_and_testBit (v all : BitVec 64) {t : Nat} (ht : t < 64)
    (hall : all.toNat.testBit t = true) :
    (~~~v &&& all).toNat.testBit t = !v.toNat.testBit t := by
  have hb : ∀ (x : BitVec 64), x.toNat.testBit t = x[t] := fun x =>
    (BitVec.getElem_eq_testBit_toNat x t ht).symm
  rw [hb (~~~v &&& all), BitVec.getElem_and, BitVec.getElem_not, ← hb v, ← hb all, hall,
    Bool.and_true]
theorem bv64_and_testBit (a b : BitVec 64) {t : Nat} (ht : t < 64) :
    (a &&& b).toNat.testBit t = (a.toNat.testBit t && b.toNat.testBit t) := by
  have hb : ∀ (x : BitVec 64), x.toNat.testBit t = x[t] := fun x =>
    (BitVec.getElem_eq_testBit_toNat x t ht).symm
  rw [hb (a &&& b), BitVec.getElem_and, ← hb a, ← hb b]
theorem litVal_cond_mask (g : Aig) (ρ : Nat → Bool) (lit : BitVec 32) (v all : BitVec 64)
    {t : Nat} (ht : t < 64) (hall : all.toNat.testBit t = true)
    (hv : v.toNat.testBit t = g.nodeVal ρ (lit >>> 1).toNat) :
    (if lit &&& 1 ≠ 0#32 then ~~~v &&& all else v).toNat.testBit t = g.litVal ρ lit.toNat := by
  rw [Aig.litVal, ← bv32_ushr1 lit, ← hv]
  by_cases h : lit &&& 1 ≠ 0#32
  · rw [ite_eq_left h, (bv32_and1_ne lit).mp h, bv64_not_and_testBit v all ht hall]; simp
  · have h0 : lit.toNat % 2 ≠ 1 := fun h1 => h ((bv32_and1_ne lit).mpr h1)
    rw [ite_eq_right h, show (lit.toNat % 2 == 1) = false from by simp [h0]]; simp

@[expose] def NodeMaskOk (g : Aig) (nleaf : Nat) (lnode : List (BitVec 32))
    (lmask : List (BitVec 64)) (all : BitVec 64) (nd : Nat) (v : BitVec 64) : Prop :=
  ∀ (t : Nat) (ρ : Nat → Bool), t < 64 → all.toNat.testBit t = true →
    (∀ j < nleaf, (lmask.getD j 0#64).toNat.testBit t = g.nodeVal ρ (lnode.getD j 0#32).toNat) →
    v.toNat.testBit t = g.nodeVal ρ nd
theorem nodeMaskOk_zero {g : Aig} {nleaf : Nat} {lnode : List (BitVec 32)}
    {lmask : List (BitVec 64)} {all : BitVec 64} :
    NodeMaskOk g nleaf lnode lmask all 0 0#64 := fun t ρ _ _ _ => by rw [g.nodeVal_zero ρ]; simp
theorem nodeMaskOk_lnode {g : Aig} {nleaf j : Nat} {lnode : List (BitVec 32)}
    {lmask : List (BitVec 64)} {all : BitVec 64} (hj : j < nleaf) :
    NodeMaskOk g nleaf lnode lmask all (lnode.getD j 0#32).toNat (lmask.getD j 0#64) :=
  fun _ _ _ _ hl => hl j hj
theorem nodeMaskOk_memo {g : Aig} {nleaf nm k : Nat} {lnode mn : List (BitVec 32)}
    {lmask mv : List (BitVec 64)} {all : BitVec 64}
    (hm : TtMemoOk g nleaf lnode lmask all nm mn mv) (hk : k < nm) :
    NodeMaskOk g nleaf lnode lmask all (mn.getD k 0#32).toNat (mv.getD k 0#64) :=
  fun t ρ ht hall hl => hm t ρ ht hall hl k hk
theorem nodeMaskOk_and {g : Aig} {rhs0 rhs1 olit : List (BitVec 32)}
    {nleaf : Nat} {lnode : List (BitVec 32)} {lmask : List (BitVec 64)} {all : BitVec 64}
    {nd : BitVec 32} {va vb : BitVec 64} (ha : AigRep g rhs0 rhs1 olit)
    (hgt : g.I < nd.toNat) (hle : nd.toNat ≤ g.M)
    (ha0 : NodeMaskOk g nleaf lnode lmask all (rhs0.getD (nd.toNat - g.I - 1) 0#32 >>> 1).toNat va)
    (hb0 :
      NodeMaskOk g nleaf lnode lmask all (rhs1.getD (nd.toNat - g.I - 1) 0#32 >>> 1).toNat vb) :
    NodeMaskOk g nleaf lnode lmask all nd.toNat
      ((if rhs0.getD (nd.toNat - g.I - 1) 0#32 &&& 1 ≠ 0#32 then ~~~va &&& all else va) &&&
       (if rhs1.getD (nd.toNat - g.I - 1) 0#32 &&& 1 ≠ 0#32 then ~~~vb &&& all else vb)) := by
  intro t ρ ht hall hleaf
  rw [bv64_and_testBit _ _ ht, ha.nodeVal_and ρ hgt hle,
    litVal_cond_mask g ρ _ va all ht hall (ha0 t ρ ht hall hleaf),
    litVal_cond_mask g ρ _ vb all ht hall (hb0 t ρ ht hall hleaf)]
theorem ttMemoOk_set {g : Aig} {nleaf nm : Nat} {lnode mn : List (BitVec 32)}
    {lmask mv : List (BitVec 64)} {all : BitVec 64} (hm : TtMemoOk g nleaf lnode lmask all nm mn mv)
    {nd : BitVec 32} {v : BitVec 64} (hmn : nm < mn.length) (hmv : nm < mv.length)
    (hv : NodeMaskOk g nleaf lnode lmask all nd.toNat v) :
    TtMemoOk g nleaf lnode lmask all (nm + 1) (mn.set nm nd) (mv.set nm v) := by
  intro t ρ ht hall hleaf k hk
  rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | hlt
  · rw [d_getD_set_eq mv 0#64 v hmv, d_getD_set_eq mn 0#32 nd hmn]; exact hv t ρ ht hall hleaf
  · rw [getD_set_ne mv 0#64 v (Nat.ne_of_lt hlt), getD_set_ne mn 0#32 nd (Nat.ne_of_lt hlt)]
    exact hm t ρ ht hall hleaf k hlt
theorem arCtxLengths_of_mem {cx : BitVec 64} {s : ArCtxState} {R : Mem 64 → Prop}
    {m : Mem 64} (hm : (arCtxMem cx s ⋆ R) m) : ArCtxLengthsOk s := by
  have hm' : (arCtxMem cx s ⋆ R) m := hm; unfold arCtxMem at hm'
  exact (sep_pure_l (φ := ArCtxLengthsOk s) (P := fun m => (arCtxTree cx s).eval m)
    (R := R) |>.mp hm').1


abbrev TtsimRest (s : ArCtxState) (rhs0 rhs1 olit : List (BitVec 32))
    (stkN0 stkP0 memoN0 : List (BitVec 32)) (dense : List (BitVec 64)) (gsy : List (BitVec 32))
    (gcl gch : List (BitVec 64)) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  arrayPad i32 s.olit olit ⋆ array64 s.dense dense ⋆ arrayPad i32 s.gsy gsy ⋆
    array64 s.gcl gcl ⋆ array64 s.gch gch ⋆ padU32 s.rhs0 rhs0.length ⋆
    padU32 s.rhs1 rhs1.length ⋆ padU32 s.stk_n stkN0.length ⋆
    padU32 s.stk_p stkP0.length ⋆ padU32 s.memo_n memoN0.length ⋆ R

abbrev TtsimMem (cx : Val i64) (s : ArCtxState)
    (rhs0 rhs1 stkN stkP memoN : List (BitVec 32)) (memoV : List (BitVec 64))
    (Rrest : Mem 64 → Prop) : Mem 64 → Prop :=
  arCtxMem cx s ⋆ array (t := i32) s.rhs0 rhs0 ⋆ array (t := i32) s.rhs1 rhs1 ⋆
    array (t := i32) s.stk_n stkN ⋆ array (t := i32) s.stk_p stkP ⋆
    array (t := i32) s.memo_n memoN ⋆ array64 s.memo_v memoV ⋆ Rrest

abbrev TtsimQ (cx : Val i64) (lit nleaf : Val i32) (all : Val i64)
    (s : ArCtxState) (g : Aig) (rhs0 rhs1 olit stkN0 stkP0 memoN0 : List (BitVec 32))
    (memoV0 dense : List (BitVec 64)) (gsy : List (BitVec 32)) (gcl gch : List (BitVec 64))
    (R : Mem 64 → Prop) (Q : Post [.bool, i64]) : Prop :=
  ∀ (ok : Bool) (v : BitVec 64) (stkN' stkP' memoN' : List (BitVec 32))
    (memoV' : List (BitVec 64)) (m' : Mem 64),
    stkN'.length = stkN0.length → stkP'.length = stkP0.length →
    memoN'.length = memoN0.length → memoV'.length = memoV0.length →
    (ok = true → ∀ (t : Nat) (ρ : Nat → Bool), t < 64 → all.toNat.testBit t = true →
      (∀ j < nleaf.toNat,
        (s.g_lmask.getD j 0#64).toNat.testBit t = g.nodeVal ρ (s.g_lnode.getD j 0#32).toNat) →
      v.toNat.testBit t = g.litVal ρ lit.toNat) →
    (arCtxMem cx s ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
     gateScratchMem s stkN' stkP' memoN' memoV' dense gsy gcl gch ⋆ R) m' → Q (ok, v, ⟨⟩) m'

abbrev TtsimG28Inv (cx : Val i64) (nleaf : Val i32) (all : Val i64)
    (s : ArCtxState) (g : Aig) (rhs0 rhs1 stkN0 stkP0 memoN0 : List (BitVec 32))
    (memoV0 : List (BitVec 64)) (Rrest : Mem 64 → Prop) (bound : Nat) :
    Tup Val [i32, i32, i32, i32] → Mem 64 → Prop
  | (sp2, nm2, nexp2, _u2, PUnit.unit), m2 =>
    sp2.toNat ≤ 160 ∧ nm2.toNat ≤ 64 ∧ nexp2.toNat ≤ 64 ∧
    3 * (64 - nexp2.toNat) + sp2.toNat < bound ∧ ∃ stkN2 stkP2 memoN2 memoV2,
      stkN2.length = stkN0.length ∧ stkP2.length = stkP0.length ∧
      memoN2.length = memoN0.length ∧ memoV2.length = memoV0.length ∧
      TtMemoOk g nleaf.toNat s.g_lnode s.g_lmask all nm2.toNat memoN2 memoV2 ∧
      TtsimMem cx s rhs0 rhs1 stkN2 stkP2 memoN2 memoV2 Rrest m2

abbrev TtsimNmInv (g : Aig) (nleaf : Val i32) (s : ArCtxState) (all : Val i64)
    (nd : Nat) (ms : Mem 64) : Tup Val [i64, Ty.bool] → Mem 64 → Prop
  | (v, f, PUnit.unit), m =>
    m = ms ∧ (f = true → NodeMaskOk g nleaf.toNat s.g_lnode s.g_lmask all nd v)
private theorem arrayPad_u32_def (a : BitVec 64) (xs : List (BitVec 32)) :
    arrayPad i32 a xs = (array (t := i32) a xs ⋆ padU32 a xs.length) := by
  rw [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray]
  dsimp only [Ty.bytes, Ty.size, Nat.reduceDiv, Nat.reduceAdd]
theorem ttsim_unpack_mem {cx : BitVec 64} {s : ArCtxState}
    {rhs0 rhs1 olit stkN0 stkP0 memoN0 : List (BitVec 32)}
    {memoV0 dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (arCtxMem cx s ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
      gateScratchMem s stkN0 stkP0 memoN0 memoV0 dense gsy gcl gch ⋆ R) m) :
    TtsimMem cx s rhs0 rhs1 stkN0 stkP0 memoN0 memoV0
      (TtsimRest s rhs0 rhs1 olit stkN0 stkP0 memoN0 dense gsy gcl gch R) m := by
  rw [aigArraysMem, gateScratchMem, arrayPad_u32_def s.rhs0 rhs0, arrayPad_u32_def s.rhs1 rhs1,
    arrayPad_u32_def s.stk_n stkN0, arrayPad_u32_def s.stk_p stkP0,
    arrayPad_u32_def s.memo_n memoN0] at hm
  dsimp only [TtsimMem, TtsimRest]; exact sep_cast hm (by ac_rfl)
theorem ttsim_repack_mem {cx : BitVec 64} {s : ArCtxState}
    {rhs0 rhs1 olit stkN0 stkP0 memoN0 stkN stkP memoN : List (BitVec 32)}
    {memoV dense : List (BitVec 64)} {gsy : List (BitVec 32)} {gcl gch : List (BitVec 64)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hsn : stkN.length = stkN0.length) (hsp : stkP.length = stkP0.length)
    (hmn : memoN.length = memoN0.length)
    (hm : (arCtxMem cx s ⋆ array (t := i32) s.rhs0 rhs0 ⋆ array (t := i32) s.rhs1 rhs1 ⋆
      array (t := i32) s.stk_n stkN ⋆ array (t := i32) s.stk_p stkP ⋆
      array (t := i32) s.memo_n memoN ⋆ array64 s.memo_v memoV ⋆
      TtsimRest s rhs0 rhs1 olit stkN0 stkP0 memoN0 dense gsy gcl gch R) m) :
    (arCtxMem cx s ⋆ aigArraysMem s rhs0 rhs1 olit ⋆
      gateScratchMem s stkN stkP memoN memoV dense gsy gcl gch ⋆ R) m := by
  rw [aigArraysMem, gateScratchMem, arrayPad_u32_def s.rhs0 rhs0, arrayPad_u32_def s.rhs1 rhs1,
    arrayPad_u32_def s.stk_n stkN, arrayPad_u32_def s.stk_p stkP, arrayPad_u32_def s.memo_n memoN,
    hsn, hsp, hmn]
  dsimp only [TtsimRest] at hm; exact sep_cast hm (by ac_rfl)
theorem nodeMaskOk_lnode_idx {g : Aig} {nleaf : Nat} {lnode : List (BitVec 32)}
    {lmask : List (BitVec 64)} {all : BitVec 64} {j : Nat} {nd : BitVec 32}
    (hj : j < nleaf) (hln : j < lnode.length) (hlm : j < lmask.length) (heq : lnode[j]'hln = nd) :
    NodeMaskOk g nleaf lnode lmask all nd.toNat (lmask[j]'hlm) := by
  rw [getElem_eq_getD 0#64 hlm rfl, ← heq, ← d_getD_eq_getElem lnode 0#32 hln]
  exact nodeMaskOk_lnode hj
theorem nodeMaskOk_memo_sw {g : Aig} {nleaf nm : Nat} {lnode mn : List (BitVec 32)}
    {lmask mv : List (BitVec 64)} {all : BitVec 64} {j nd : BitVec 32}
    (hm : TtMemoOk g nleaf lnode lmask all nm mn mv) (hj : j.toNat < nm)
    (hmn : (BitVec.setWidth 64 j).toNat < mn.length)
    (hmv : (BitVec.setWidth 64 j).toNat < mv.length)
    (heq : mn[(BitVec.setWidth 64 j).toNat]'hmn = nd) :
    NodeMaskOk g nleaf lnode lmask all nd.toNat (mv[(BitVec.setWidth 64 j).toNat]'hmv) := by
  rw [getElem_eq_getD 0#64 hmv bv64_sw_toNat, ← heq, getElem_eq_getD 0#32 hmn bv64_sw_toNat]
  exact nodeMaskOk_memo hm hj
theorem ttsim_neg_branch_t {v all : BitVec 64} {x : BitVec 32} (hc : x &&& 1 ≠ 0#32) :
    (~~~v &&& all) = if x &&& 1 ≠ 0#32 then ~~~v &&& all else v := by rw [ite_eq_left hc]
theorem ttsim_neg_branch_f {v all : BitVec 64} {x : BitVec 32} (hc : x &&& 1 = 0#32) :
    v = if x &&& 1 ≠ 0#32 then ~~~v &&& all else v := by rw [ite_eq_right (fun h => h hc)]

@[expose] def evalTtsimOp : {rs : List Ty} → Op Val rs → Option (Tup Val rs)
  | [.bits 64], ⟨.sext 32 64, (a, ())⟩ => some (BitVec.signExtend 64 a.val, ())
  | [.bits 64], ⟨.zext 32 64, (a, ())⟩ => some (BitVec.setWidth 64 a.val, ())
  | [.bits 64], ⟨.add (.bits 64), (a, b, ())⟩ => some (a.val + b.val, ())
  | [.bits 64], ⟨.mul (.bits 64), (a, b, ())⟩ => some (a.val * b.val, ())
  | [.bits 32], ⟨.sub (.bits 32), (a, b, ())⟩ => some (a.val - b.val, ())
  | [.bits 32], ⟨.lshr (.bits 32), (a, b, ())⟩ => some (a.val >>> b.val.toNat, ())
  | _, _ => none

@[expose] def ttsimOuterGo (sn sph mn mv : Val i64) :
    Nat → Nat → Expr Val Cont [.bool, i64] → Expr Val Cont [.bool, i64]
  | lds, sts, .let_ op k =>
    match evalTtsimOp op with | some r => ttsimOuterGo sn sph mn mv lds sts (k r) | none => .hlt
  | 0, sts, .load (.bits 64) _ k => ttsimOuterGo sn sph mn mv 1 sts (k sn)
  | 1, sts, .load (.bits 64) _ k => ttsimOuterGo sn sph mn mv 2 sts (k sph)
  | 2, sts, .load (.bits 64) _ k => ttsimOuterGo sn sph mn mv 3 sts (k mn)
  | 3, sts, .load (.bits 64) _ k => ttsimOuterGo sn sph mn mv 4 sts (k mv)
  | lds, sts, .store _ _ k => ttsimOuterGo sn sph mn mv lds (sts + 1) k
  | _, _, e => e

@[expose] def ttsimOuter (cx : Val i64) (lit nleaf : Val i32) (all sn sph mn mv : Val i64) :
    Expr Val Cont [.bool, i64] :=
  ttsimOuterGo sn sph mn mv 0 0 (ar_ttsim_body Val Cont (cx, lit, nleaf, all, ()))

@[expose] def ttsimExit (cx : Val i64) (lit nleaf : Val i32) (all sn sph mn mv : Val i64)
    (sp nm nexp : Val i32) : Expr Val Cont [.bool, i64] :=
  match ttsimOuter cx lit nleaf all sn sph mn mv with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 32]] bs _ => match bs (fun _ _ => False, ()) with
    | .cons b _ => match b (sp, nm, nexp, ()) with
      | @Expr.let_ _ _ _ [.bool] _ kc => match kc (false, ()) with | .jnz _ _ f => f | _ => .hlt
      | _ => .hlt
    | _ => .hlt
  | _ => .hlt

end

end LeanQbe.T.Examples.Arisca.Proof

/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Arisca.Proof.Poly2Base
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas
import Kraken.Separation

/-!
# ARiSCA `ar_build_R` Pure Algebra, Bounds & Memory Helpers (`Arisca.Proof.Poly2RBase`)

Pure definitions and lemmas supporting `ar_build_R_wp`:
- Symbol index bound `SymsBound` for unguarded `flipped[x >> 1]` lookups
- Flip counting (`flipCond`, `flipCount`) and Pass 1 `bt` / `bw` overflow bounds
- Deduplicating push (`dedupPush`) and sign-alternating subset expansion (`expandStep`,
  `expandSum`, `expandSum_eq`)
- Complemented-rule evaluation (`rules_flipped_eval`), Pass 4 `CombineRInv`, `rMem` focus
  lemmas, and `u32`/`u64` bit bridges.
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

/-! ## 1. `SymsBound`, Flip Counting & Expansion Algebra -/

@[expose] public section

/-- Flip predicate matching C0 `(x & 1u) == 0u && cx->flipped[x >> 1] != 0`. -/
def flipCond (flippedArr : List (BitVec 8)) (x : Nat) : Bool :=
  (x % 2 == 0) && (flippedArr.getD (x / 2) 0#8 != 0#8)

/-- Number of flippable positive literals in monomial `xs`. -/
def flipCount (flippedArr : List (BitVec 8)) (xs : List Nat) : Nat :=
  xs.foldl (fun f x => if flipCond flippedArr x then f + 1 else f) 0

/-- Append `x` to `acc` only if different from the last emitted symbol
(`k > 1 && out[k-1] == x`). -/
def dedupPush (acc : List Nat) (x : Nat) : List Nat :=
  if acc.getLast? = some x then acc else acc ++ [x]

/-- One step of the Pass 2 subset-expansion `j` loop for assignment mask `S`. -/
def expandStep (flippedArr : List (BitVec 8)) (S : Nat)
    (st : List Nat × Nat × Nat) (x : Nat) : List Nat × Nat × Nat :=
  let (acc, fi, par) := st
  if flipCond flippedArr x then
    if (S / 2 ^ fi) % 2 = 0 then (acc, fi + 1, par)
    else (dedupPush acc (x + 1), fi + 1, par ^^^ 1)
  else
    (dedupPush acc x, fi, par)

/-- Signed coefficient-times-monomial value contributed by subset `S`. -/
def expandTermEval (nOut : Nat) (σ : Nat → Bool) (flippedArr : List (BitVec 8))
    (c : BitVec nOut) (S : Nat) (acc : List Nat) (fi par : Nat) (xs : List Nat) : BitVec nOut :=
  let res := xs.foldl (expandStep flippedArr S) (acc, fi, par)
  let cs := if res.2.2 % 2 = 1 then -c else c
  if monoValL σ res.1 then cs else 0#nOut

/-- Sum of `expandTermEval` over all `2 ^ flipCount flippedArr xs` subsets `S`. -/
def expandSum (nOut : Nat) (σ : Nat → Bool) (flippedArr : List (BitVec 8))
    (c : BitVec nOut) (acc : List Nat) (par : Nat) (xs : List Nat) : BitVec nOut :=
  (List.range (2 ^ flipCount flippedArr xs)).foldl
    (fun sum S => sum + expandTermEval nOut σ flippedArr c S acc 0 par xs) 0#nOut

/-- Pass 1 expanded term count contribution over `cnt` monomials starting at `off`. -/
def ruleBt8 (flippedArr : List (BitVec 8)) (rsPool rsM : List (BitVec 32))
    (off cnt : Nat) : Nat :=
  (List.range cnt).foldl
    (fun acc i => acc + 2 ^ flipCount flippedArr (symListAt rsPool (rsM.getD (off + i) 0#32).toNat))
    0

/-- Pass 1 expanded word count contribution over `cnt` monomials starting at `off`. -/
def ruleBw8 (flippedArr : List (BitVec 8)) (rsPool rsM : List (BitVec 32))
    (off cnt : Nat) : Nat :=
  (List.range cnt).foldl
    (fun acc i =>
      let mOff := (rsM.getD (off + i) 0#32).toNat
      acc + 2 ^ flipCount flippedArr (symListAt rsPool mOff) * ((rsPool.getD mOff 0#32).toNat + 1))
    0

/-- Loop invariant for Pass 4 deduplicating/combining sorted `ix[0..n)` into `(rm2, rl2, rh2)`. -/
def CombineRInv (nOut : Nat) (σ : Nat → Bool) (rpool rm : List (BitVec 32))
    (rl rh : List (BitVec 64)) (aArr : List (BitVec 32)) (n rcap : Nat)
    (rm2Ptr rl2Ptr rh2Ptr : BitVec 64) (Rcmb : Mem 64 → Prop) (k2 i : Nat) (mC : Mem 64) : Prop :=
  ∃ (rm2C : List (BitVec 32)) (rl2C rh2C : List (BitVec 64)),
    rcap ≤ rm2C.length ∧ rcap ≤ rl2C.length ∧ rcap ≤ rh2C.length ∧
    k2 ≤ i ∧ i ≤ n ∧
    (∀ p < k2, ∃ idx < n, rm2C.getD p 0#32 = rm.getD idx 0#32) ∧
    polyEval nOut σ rpool rm2C rl2C rh2C k2 +
      polyEvalIdxOf nOut σ rpool rm rl rh aArr i (n - i) =
      polyEval nOut σ rpool rm rl rh n ∧
    (array (t := i32) rm2Ptr rm2C ⋆ array64 rl2Ptr rl2C ⋆
      array64 rh2Ptr rh2C ⋆ Rcmb) mC

end

public section

theorem SymsBound.congr_prefix {pool1 pool2 mOff1 mOff2 : List (BitVec 32)} {bdPool n bd : Nat}
    (hSb : SymsBound pool1 mOff1 n bd)
    (hSl : ∀ i < n, MonoSliceOk pool1 (mOff1.getD i 0#32).toNat bdPool)
    (hP : ∀ idx < bdPool, pool2.getD idx 0#32 = pool1.getD idx 0#32)
    (hM : ∀ i < n, mOff2.getD i 0#32 = mOff1.getD i 0#32) :
    SymsBound pool2 mOff2 n bd := by
  intro i hi x hx
  have hsn := hSl i hi
  have hsy : symListAt pool2 (mOff2.getD i 0#32).toNat =
      symListAt pool1 (mOff1.getD i 0#32).toNat := by
    rw [hM i hi]
    simp only [symListAt, hP _ hsn.1]
    apply List.map_congr_left
    intro k hk
    have hlt := List.mem_range.mp hk
    have hbd := hsn.2
    rw [hP _ (by omega)]
  rw [hsy] at hx
  exact hSb i hi x hx

theorem SymsBound.mono_range {pool mOff : List (BitVec 32)} {n bd off cnt : Nat}
    (hSb : SymsBound pool mOff n bd) (hbd : off + cnt ≤ n) :
    ∀ i < cnt, ∀ x ∈ symListAt pool (mOff.getD (off + i) 0#32).toNat, x / 2 < bd :=
  fun i hi => hSb (off + i) (by omega)

private theorem foldl_flipCount_init (flippedArr : List (BitVec 8)) (xs : List Nat) (init : Nat) :
    xs.foldl (fun f x => if flipCond flippedArr x then f + 1 else f) init =
      init + flipCount flippedArr xs := by
  induction xs generalizing init with
  | nil => simp [flipCount]
  | cons x xs ih =>
    dsimp only [flipCount, List.foldl_cons]
    cases hc : flipCond flippedArr x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih init
    · simp only [↓reduceIte]
      have h1 := ih 1
      dsimp only [flipCount] at h1
      rw [ih (init + 1)]
      dsimp only [flipCount]
      rw [h1]
      omega

theorem flipCount_nil (flippedArr : List (BitVec 8)) : flipCount flippedArr [] = 0 := rfl

theorem flipCount_cons (flippedArr : List (BitVec 8)) (x : Nat) (xs : List Nat) :
    flipCount flippedArr (x :: xs) =
      (if flipCond flippedArr x then 1 else 0) + flipCount flippedArr xs := by
  dsimp only [flipCount, List.foldl_cons]
  rw [foldl_flipCount_init]
  split <;> rfl

theorem flipCount_append (flippedArr : List (BitVec 8)) (xs ys : List Nat) :
    flipCount flippedArr (xs ++ ys) =
      flipCount flippedArr xs + flipCount flippedArr ys := by
  induction xs with
  | nil => simp [flipCount_nil]
  | cons x xs ih => rw [List.cons_append, flipCount_cons, flipCount_cons, ih, Nat.add_assoc]

theorem flipCount_le_length (flippedArr : List (BitVec 8)) (xs : List Nat) :
    flipCount flippedArr xs ≤ xs.length := by
  induction xs with
  | nil => simp [flipCount_nil]
  | cons x xs ih =>
    rw [flipCount_cons, List.length_cons]
    split <;> omega

theorem monoValL_append (σ : Nat → Bool) (xs ys : List Nat) :
    monoValL σ (xs ++ ys) = (monoValL σ xs && monoValL σ ys) := by
  induction xs with
  | nil => simp [monoValL]
  | cons x xs ih => simp [monoValL, ih, Bool.and_assoc]

theorem monoValL_dedupPush (σ : Nat → Bool) (acc : List Nat) (x : Nat) :
    monoValL σ (dedupPush acc x) = (monoValL σ acc && σ x) := by
  unfold dedupPush
  by_cases h : acc.getLast? = some x
  · rw [ite_eq_left h]
    have hx : x ∈ acc := List.mem_of_getLast? h
    rw [monoValL_eq_decide]
    cases hσ : σ x
    · simp only [Bool.and_false, decide_eq_false_iff_not]
      intro hall; exact absurd (hall x hx) (by rw [hσ]; decide)
    · simp
  · rw [ite_eq_right h, monoValL_append, monoValL_cons, monoValL_nil, Bool.and_true]

theorem dedupPush_length_le (acc : List Nat) (x : Nat) :
    (dedupPush acc x).length ≤ acc.length + 1 := by
  unfold dedupPush
  split <;> simp

theorem mem_dedupPush (acc : List Nat) (x y : Nat) :
    y ∈ dedupPush acc x → y ∈ acc ∨ y = x := by
  unfold dedupPush
  split
  · exact Or.inl
  · intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.mp h2)

theorem expandFold_shift (flippedArr : List (BitVec 8)) (S d : Nat)
    (xs acc : List Nat) (fi par : Nat) :
    let r1 := xs.foldl (expandStep flippedArr S) (acc, fi + d, par)
    let r2 := xs.foldl (expandStep flippedArr (S / 2 ^ d)) (acc, fi, par)
    r1.1 = r2.1 ∧ r1.2.1 = r2.2.1 + d ∧ r1.2.2 = r2.2.2 := by
  induction xs generalizing acc fi par with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons, expandStep]
    have hbit : (S / 2 ^ (fi + d)) % 2 = ((S / 2 ^ d) / 2 ^ fi) % 2 := by
      rw [Nat.pow_add, Nat.mul_comm (2 ^ fi) (2 ^ d), ← Nat.div_div_eq_div_mul]
    rw [hbit]
    by_cases hf : flipCond flippedArr x
    · simp only [hf, ↓reduceIte]
      by_cases hb : ((S / 2 ^ d) / 2 ^ fi) % 2 = 0
      · simp only [hb, ↓reduceIte]
        simpa only [Nat.succ_add] using ih acc (fi + 1) par
      · simp only [hb, ↓reduceIte]
        simpa only [Nat.succ_add] using ih (dedupPush acc (x + 1)) (fi + 1) (par ^^^ 1)
    · simp only [hf, Bool.false_eq_true, ↓reduceIte]
      exact ih (dedupPush acc x) fi par

theorem expandFold_len_le (flippedArr : List (BitVec 8)) (S : Nat)
    (xs acc : List Nat) (fi par : Nat) :
    (xs.foldl (expandStep flippedArr S) (acc, fi, par)).1.length ≤ acc.length + xs.length := by
  induction xs generalizing acc fi par with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, expandStep, List.length_cons]
    split
    · split
      · have := ih acc (fi + 1) par; omega
      · have := ih (dedupPush acc (x + 1)) (fi + 1) (par ^^^ 1)
        have hd := dedupPush_length_le acc (x + 1); omega
    · have := ih (dedupPush acc x) fi par
      have hd := dedupPush_length_le acc x; omega

theorem expandFold_symsBound (flippedArr : List (BitVec 8)) (S bd : Nat)
    (xs acc : List Nat) (fi par : Nat)
    (hacc : ∀ z ∈ acc, z / 2 < bd) (hxs : ∀ x ∈ xs, x / 2 < bd) :
    ∀ y ∈ (xs.foldl (expandStep flippedArr S) (acc, fi, par)).1, y / 2 < bd := by
  induction xs generalizing acc fi par with
  | nil => exact hacc
  | cons x xs ih =>
    simp only [List.foldl_cons, expandStep]
    have hx := hxs x (List.Mem.head _)
    have hxs' : ∀ z ∈ xs, z / 2 < bd := fun z hz => hxs z (List.Mem.tail _ hz)
    by_cases hf : flipCond flippedArr x
    · simp only [hf, ↓reduceIte]
      by_cases hb : (S / 2 ^ fi) % 2 = 0
      · simp only [hb, ↓reduceIte]; exact ih acc (fi + 1) par hacc hxs'
      · simp only [hb, ↓reduceIte]
        have hx0 : x % 2 = 0 := by
          simp only [flipCond, Bool.and_eq_true, beq_iff_eq] at hf
          exact hf.1
        apply ih (dedupPush acc (x + 1)) (fi + 1) (par ^^^ 1) _ hxs'
        intro y hy
        rcases mem_dedupPush acc (x + 1) y hy with ha | rfl
        · exact hacc y ha
        · omega
    · simp only [hf, Bool.false_eq_true, ↓reduceIte]
      apply ih (dedupPush acc x) fi par _ hxs'
      intro y hy
      rcases mem_dedupPush acc x y hy with ha | rfl
      · exact hacc y ha
      · exact hx

private theorem foldl_range_double {w : Nat} (n : Nat) (f : Nat → BitVec w) :
    (List.range (2 * n)).foldl (fun acc k => acc + f k) 0#w =
      (List.range n).foldl (fun acc k => acc + f (2 * k)) 0#w +
        (List.range n).foldl (fun acc k => acc + f (2 * k + 1)) 0#w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, List.range_succ, List.range_succ,
      List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
      List.foldl_nil, ih]
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
      List.foldl_nil, List.foldl_nil]
    ac_rfl

private theorem foldl_range_add_congr {w : Nat} (n : Nat) (f g : Nat → BitVec w)
    (h : ∀ k < n, f k = g k) :
    (List.range n).foldl (fun acc k => acc + f k) 0#w =
      (List.range n).foldl (fun acc k => acc + g k) 0#w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

private theorem xor_one_mod2_eq (p : Nat) :
    ((p ^^^ 1) % 2 = 1) ↔ (p % 2 ≠ 1) := by
  have hx : p ^^^ 1 = if p % 2 = 0 then p + 1 else p - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero =>
      simp only [Nat.testBit_zero]
      by_cases h0 : p % 2 = 0 <;> simp [h0] <;> omega
    | succ i =>
      have hb1 : (1 : Nat).testBit (i + 1) = false := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow,
          Nat.div_eq_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero i) (by decide))]
        decide
      rw [Nat.testBit_xor, hb1, Bool.xor_false]
      by_cases h0 : p % 2 = 0
      · simp only [h0, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
        congr 1
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, ← Nat.div_div_eq_div_mul,
          ← Nat.div_div_eq_div_mul, show (p + 1) / 2 = p / 2 by omega]
      · simp only [h0, ↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow]
        congr 1
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, ← Nat.div_div_eq_div_mul,
          ← Nat.div_div_eq_div_mul, show (p - 1) / 2 = p / 2 by omega]
  rw [hx]
  by_cases h0 : p % 2 = 0 <;> simp [h0] <;> omega

private theorem bv_mul_bool {w : Nat} (c : BitVec w) (b : Bool) :
    (if b then c else 0#w) = c * bv w b := by
  cases b <;> simp [bv]

private theorem bv_and {w : Nat} (a b : Bool) : bv w (a && b) = bv w a * bv w b := by
  cases a <;> cases b <;> simp [bv]

private theorem bv_sub_not {w : Nat} (b : Bool) : bv w true - bv w b = bv w (!b) := by
  cases b <;> simp [bv]

theorem expandSum_eq (nOut bd : Nat) (σ : Nat → Bool) (flippedArr : List (BitVec 8))
    (c : BitVec nOut) (acc : List Nat) (par : Nat) (xs : List Nat)
    (hσ : ∀ w < bd, σ (2 * w + 1) = !(σ (2 * w)))
    (hxs : ∀ x ∈ xs, x / 2 < bd) :
    expandSum nOut σ flippedArr c acc par xs =
      (if par % 2 = 1 then -c else c) * bv nOut (monoValL σ acc && monoValL σ xs) := by
  induction xs generalizing acc par with
  | nil =>
    simp only [expandSum, flipCount_nil, Nat.pow_zero, List.range_one, List.foldl_cons,
      List.foldl_nil, BitVec.zero_add, expandTermEval, monoValL_nil, Bool.and_true]
    exact bv_mul_bool _ _
  | cons x xs ih =>
    have hx := hxs x (List.Mem.head _)
    have hxs' : ∀ z ∈ xs, z / 2 < bd := fun z hz => hxs z (List.Mem.tail _ hz)
    by_cases hf : flipCond flippedArr x
    · have hf_even : x % 2 = 0 := by
        simp only [flipCond, Bool.and_eq_true, beq_iff_eq] at hf
        exact hf.1
      have hxsig : (!(σ (x + 1))) = σ x := by
        have hx2 : 2 * (x / 2) = x := by omega
        have hw := hσ (x / 2) hx
        rw [hx2] at hw
        rw [hw, Bool.not_not]
      have hfc : flipCount flippedArr (x :: xs) = 1 + flipCount flippedArr xs := by
        rw [flipCount_cons, ite_eq_left hf]
      have hpow : 2 ^ flipCount flippedArr (x :: xs) = 2 * 2 ^ flipCount flippedArr xs := by
        rw [hfc, Nat.pow_add, Nat.pow_one]
      have heven_eq : ∀ S < 2 ^ flipCount flippedArr xs,
          expandTermEval nOut σ flippedArr c (2 * S) acc 0 par (x :: xs) =
            expandTermEval nOut σ flippedArr c S acc 0 par xs := by
        intro S _
        simp only [expandTermEval, List.foldl_cons, expandStep, hf, ↓reduceIte, Nat.pow_zero,
          Nat.div_one, Nat.mul_mod_right]
        have hsh := expandFold_shift flippedArr (2 * S) 1 xs acc 0 par
        rw [show (2 * S) / 2 ^ 1 = S by omega, show (0 + 1 : Nat) = 1 from rfl] at hsh
        dsimp only at hsh
        rw [hsh.1, hsh.2.2]
      have hodd_eq : ∀ S < 2 ^ flipCount flippedArr xs,
          expandTermEval nOut σ flippedArr c (2 * S + 1) acc 0 par (x :: xs) =
            expandTermEval nOut σ flippedArr c S (dedupPush acc (x + 1)) 0 (par ^^^ 1) xs := by
        intro S _
        simp only [expandTermEval, List.foldl_cons, expandStep, hf, ↓reduceIte, Nat.pow_zero,
          Nat.div_one, show (2 * S + 1) % 2 = 1 by omega, show ¬ (1 : Nat) = 0 by decide,
          Nat.zero_add]
        have hsh := expandFold_shift flippedArr (2 * S + 1) 1 xs
          (dedupPush acc (x + 1)) 0 (par ^^^ 1)
        rw [show (2 * S + 1) / 2 ^ 1 = S by omega, show (0 + 1 : Nat) = 1 from rfl] at hsh
        dsimp only at hsh
        rw [hsh.1, hsh.2.2]
      rw [expandSum, hpow, foldl_range_double]
      rw [foldl_range_add_congr _ _ _ heven_eq, foldl_range_add_congr _ _ _ hodd_eq]
      change expandSum nOut σ flippedArr c acc par xs +
          expandSum nOut σ flippedArr c (dedupPush acc (x + 1)) (par ^^^ 1) xs = _
      rw [ih acc par hxs', ih (dedupPush acc (x + 1)) (par ^^^ 1) hxs',
        monoValL_dedupPush, monoValL_cons, bv_and, bv_and, bv_and, bv_and, bv_and]
      have hneg_coeff : (if (par ^^^ 1) % 2 = 1 then -c else c) =
          -(if par % 2 = 1 then -c else c) := by
        by_cases hp : par % 2 = 1
        · have hp' : ¬ (par ^^^ 1) % 2 = 1 :=
            fun h => ((xor_one_mod2_eq par).mp h) hp
          simp [hp, hp']
        · have hp' : (par ^^^ 1) % 2 = 1 := (xor_one_mod2_eq par).mpr hp
          simp [hp, hp']
      rw [hneg_coeff, ← hxsig]
      let cs := if par % 2 = 1 then -c else c
      change cs * (bv nOut (monoValL σ acc) * bv nOut (monoValL σ xs)) +
          -cs * (bv nOut (monoValL σ acc) * bv nOut (σ (x + 1)) * bv nOut (monoValL σ xs)) =
        cs * (bv nOut (monoValL σ acc) * (bv nOut (!(σ (x + 1))) * bv nOut (monoValL σ xs)))
      rw [← bv_sub_not (σ (x + 1)), show bv nOut true = 1#nOut from rfl]
      grind
    · have hfc : flipCount flippedArr (x :: xs) = flipCount flippedArr xs := by
        rw [flipCount_cons, ite_eq_right hf, Nat.zero_add]
      have hterm : ∀ S < 2 ^ flipCount flippedArr xs,
          expandTermEval nOut σ flippedArr c S acc 0 par (x :: xs) =
            expandTermEval nOut σ flippedArr c S (dedupPush acc x) 0 par xs := by
        intro S _
        simp only [expandTermEval, List.foldl_cons, expandStep, hf, Bool.false_eq_true, ↓reduceIte]
      rw [expandSum, hfc, foldl_range_add_congr _ _ _ hterm]
      change expandSum nOut σ flippedArr c (dedupPush acc x) par xs = _
      rw [ih (dedupPush acc x) par hxs', monoValL_dedupPush, monoValL_cons, Bool.and_assoc]

theorem ruleBt8_succ (flippedArr : List (BitVec 8)) (rsPool rsM : List (BitVec 32))
    (off cnt : Nat) :
    ruleBt8 flippedArr rsPool rsM off (cnt + 1) =
      ruleBt8 flippedArr rsPool rsM off cnt +
        2 ^ flipCount flippedArr (symListAt rsPool (rsM.getD (off + cnt) 0#32).toNat) := by
  simp only [ruleBt8, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ruleBw8_succ (flippedArr : List (BitVec 8)) (rsPool rsM : List (BitVec 32))
    (off cnt : Nat) :
    ruleBw8 flippedArr rsPool rsM off (cnt + 1) =
      ruleBw8 flippedArr rsPool rsM off cnt +
        2 ^ flipCount flippedArr (symListAt rsPool (rsM.getD (off + cnt) 0#32).toNat) *
          ((rsPool.getD (rsM.getD (off + cnt) 0#32).toNat 0#32).toNat + 1) := by
  simp only [ruleBw8, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem monoTotalWords_range_le (pool tm : List (BitVec 32)) (off cnt n : Nat)
    (hle : off + cnt ≤ n) :
    (List.range cnt).foldl
      (fun acc i => acc + ((pool.getD (tm.getD (off + i) 0#32).toNat 0#32).toNat + 1)) 0 ≤
      monoTotalWords pool tm n := by
  have hpref : ∀ a b : Nat, a ≤ b → monoTotalWords pool tm a ≤ monoTotalWords pool tm b := by
    intro a b hab
    induction hab with
    | refl => exact le_refl _
    | step _ ih => rw [monoTotalWords_succ]; omega
  have hsub : (List.range cnt).foldl
      (fun acc i => acc + ((pool.getD (tm.getD (off + i) 0#32).toNat 0#32).toNat + 1)) 0 ≤
      monoTotalWords pool tm (off + cnt) := by
    induction cnt with
    | zero => simp [monoTotalWords]
    | succ cnt ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        show off + (cnt + 1) = (off + cnt) + 1 by omega, monoTotalWords_succ]
      have := ih (by omega)
      omega
  exact Nat.le_trans hsub (hpref _ _ hle)

theorem ruleBt8_le (flippedArr : List (BitVec 8)) (rsPool rsM : List (BitVec 32))
    (off cnt : Nat) (hF : ∀ i < cnt, flipCount flippedArr
      (symListAt rsPool (rsM.getD (off + i) 0#32).toNat) ≤ arRMaxF) :
    ruleBt8 flippedArr rsPool rsM off cnt ≤ cnt * 2 ^ arRMaxF := by
  induction cnt with
  | zero => simp [ruleBt8]
  | succ cnt ih =>
    rw [ruleBt8_succ, Nat.succ_mul]
    have h1 := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have h2 : 2 ^ flipCount flippedArr
        (symListAt rsPool (rsM.getD (off + cnt) 0#32).toNat) ≤ 2 ^ arRMaxF :=
      Nat.pow_le_pow_right (by decide) (hF cnt (Nat.lt_succ_self cnt))
    omega

theorem ruleBw8_le (flippedArr : List (BitVec 8)) (rsPool rsM : List (BitVec 32))
    (off cnt : Nat) (hF : ∀ i < cnt, flipCount flippedArr
      (symListAt rsPool (rsM.getD (off + i) 0#32).toNat) ≤ arRMaxF) :
    ruleBw8 flippedArr rsPool rsM off cnt ≤
      2 ^ arRMaxF * (List.range cnt).foldl
        (fun acc i => acc + ((rsPool.getD (rsM.getD (off + i) 0#32).toNat 0#32).toNat + 1)) 0 := by
  induction cnt with
  | zero => simp [ruleBw8]
  | succ cnt ih =>
    rw [ruleBw8_succ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h1 := ih (fun i hi => hF i (Nat.lt_succ_of_lt hi))
    have h2 : 2 ^ flipCount flippedArr
        (symListAt rsPool (rsM.getD (off + cnt) 0#32).toNat) ≤ 2 ^ arRMaxF :=
      Nat.pow_le_pow_right (by decide) (hF cnt (Nat.lt_succ_self cnt))
    have h3 : 2 ^ flipCount flippedArr (symListAt rsPool (rsM.getD (off + cnt) 0#32).toNat) *
          ((rsPool.getD (rsM.getD (off + cnt) 0#32).toNat 0#32).toNat + 1) ≤
        2 ^ arRMaxF * ((rsPool.getD (rsM.getD (off + cnt) 0#32).toNat 0#32).toNat + 1) :=
      Nat.mul_le_mul_right _ h2
    have hsum := Nat.add_le_add h1 h3
    rw [← Nat.mul_add] at hsum
    simpa only [Nat.add_assoc] using hsum

theorem rules_flipped_eval (nOut v : Nat) (σ : Nat → Bool)
    (rsPool rsM : List (BitVec 32)) (rsL rsH : List (BitVec 64)) (off cnt : Nat)
    (fv_b : Bool) (hσ : σ (2 * v + 1) = !(σ (2 * v)))
    (hRule : bv nOut (σ (2 * v)) = polyEvalRange nOut σ rsPool rsM rsL rsH off cnt) :
    (if fv_b then 1#nOut else 0#nOut) +
      (if fv_b then -polyEvalRange nOut σ rsPool rsM rsL rsH off cnt
        else polyEvalRange nOut σ rsPool rsM rsL rsH off cnt) =
      bv nOut (σ (if fv_b then 2 * v + 1 else 2 * v)) := by
  cases fv_b
  · simp [← hRule]
  · simp only [↓reduceIte, ← hRule, hσ]
    rw [show (1#nOut : BitVec nOut) = bv nOut true from rfl, ← BitVec.sub_eq_add_neg, bv_sub_not]

/-! ## 2. `rMem` Focus, Bitwise & Pass 2/4 Helpers -/

theorem rMem_unfold (s : ArCtxState) (rm : List (BitVec 32)) (rl rh : List (BitVec 64))
    (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64)) (rpool : List (BitVec 32)) :
    rMem s rm rl rh rm2 rl2 rh2 rpool =
      (array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
       array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆ array64 s.rh2 rh2 ⋆
       array (t := i32) s.rpool rpool ⋆
       u32PadTail s.rm rm.length ⋆ u32PadTail s.rm2 rm2.length ⋆
       u32PadTail s.rpool rpool.length) := by
  simp only [rMem, arrayPad_u32_unfold]; ac_rfl

/-- Packed read-only memory frame during `ar_build_R` Pass 2 (`rm, rl, rh, rpool` live outside). -/
@[expose] def buildRPass2Ro (s : ArCtxState) (ruleOff ruleN rsM : List (BitVec 32))
    (rsL rsH : List (BitVec 64)) (rsPool : List (BitVec 32)) (flippedArr : List (BitVec 8))
    (rmLen rpoolLen : Nat) (rm2 : List (BitVec 32)) (rl2 rh2 : List (BitVec 64))
    (R : Mem 64 → Prop) : Mem 64 → Prop :=
  array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
  array (t := i8) s.flipped flippedArr ⋆ array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆
  array64 s.rs_h rsH ⋆ array (t := i32) s.rs_pool rsPool ⋆ u32PadTail s.rs_m rsM.length ⋆
  u32PadTail s.rs_pool rsPool.length ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
  array64 s.rh2 rh2 ⋆ u32PadTail s.rm rmLen ⋆ u32PadTail s.rm2 rm2.length ⋆
  u32PadTail s.rpool rpoolLen ⋆ R

theorem buildR_pass2_pack {cx : BitVec 64} {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rm : List (BitVec 32)} {rl rh : List (BitVec 64)} {rm2 : List (BitVec 32)}
    {rl2 rh2 : List (BitVec 64)} {rpool : List (BitVec 32)} {R : Mem 64 → Prop} :
    (arCtxMem cx s ⋆ array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
      array (t := i8) s.flipped flippedArr ⋆ rsMem s rsM rsL rsH rsPool ⋆
      rMem s rm rl rh rm2 rl2 rh2 rpool ⋆ R) =
    (arCtxMem cx s ⋆ array (t := i32) s.rm rm ⋆ array64 s.rl rl ⋆ array64 s.rh rh ⋆
      array (t := i32) s.rpool rpool ⋆
      buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rm.length rpool.length
        rm2 rl2 rh2 R) := by
  rw [rsMem_unfold, rMem_unfold]
  dsimp only [buildRPass2Ro]
  ac_rfl

theorem buildRPass2Ro_flipped {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rmLen rpoolLen : Nat} {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {R : Mem 64 → Prop} :
    ∃ rest, buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rmLen rpoolLen
      rm2 rl2 rh2 R = (array (t := i8) s.flipped flippedArr ⋆ rest) :=
  ⟨array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
    array (t := i32) s.rs_pool rsPool ⋆ u32PadTail s.rs_m rsM.length ⋆
    u32PadTail s.rs_pool rsPool.length ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
    array64 s.rh2 rh2 ⋆ u32PadTail s.rm rmLen ⋆ u32PadTail s.rm2 rm2.length ⋆
    u32PadTail s.rpool rpoolLen ⋆ R, by dsimp only [buildRPass2Ro]; ac_rfl⟩

theorem buildRPass2Ro_rsM {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rmLen rpoolLen : Nat} {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {R : Mem 64 → Prop} :
    ∃ rest, buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rmLen rpoolLen
      rm2 rl2 rh2 R = (array (t := i32) s.rs_m rsM ⋆ rest) :=
  ⟨array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i8) s.flipped flippedArr ⋆ array64 s.rs_l rsL ⋆ array64 s.rs_h rsH ⋆
    array (t := i32) s.rs_pool rsPool ⋆ u32PadTail s.rs_m rsM.length ⋆
    u32PadTail s.rs_pool rsPool.length ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
    array64 s.rh2 rh2 ⋆ u32PadTail s.rm rmLen ⋆ u32PadTail s.rm2 rm2.length ⋆
    u32PadTail s.rpool rpoolLen ⋆ R, by dsimp only [buildRPass2Ro]; ac_rfl⟩

theorem buildRPass2Ro_rsL {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rmLen rpoolLen : Nat} {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {R : Mem 64 → Prop} :
    ∃ rest, buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rmLen rpoolLen
      rm2 rl2 rh2 R = (array64 s.rs_l rsL ⋆ rest) :=
  ⟨array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i8) s.flipped flippedArr ⋆ array (t := i32) s.rs_m rsM ⋆ array64 s.rs_h rsH ⋆
    array (t := i32) s.rs_pool rsPool ⋆ u32PadTail s.rs_m rsM.length ⋆
    u32PadTail s.rs_pool rsPool.length ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
    array64 s.rh2 rh2 ⋆ u32PadTail s.rm rmLen ⋆ u32PadTail s.rm2 rm2.length ⋆
    u32PadTail s.rpool rpoolLen ⋆ R, by dsimp only [buildRPass2Ro]; ac_rfl⟩

theorem buildRPass2Ro_rsH {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rmLen rpoolLen : Nat} {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {R : Mem 64 → Prop} :
    ∃ rest, buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rmLen rpoolLen
      rm2 rl2 rh2 R = (array64 s.rs_h rsH ⋆ rest) :=
  ⟨array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i8) s.flipped flippedArr ⋆ array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆
    array (t := i32) s.rs_pool rsPool ⋆ u32PadTail s.rs_m rsM.length ⋆
    u32PadTail s.rs_pool rsPool.length ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
    array64 s.rh2 rh2 ⋆ u32PadTail s.rm rmLen ⋆ u32PadTail s.rm2 rm2.length ⋆
    u32PadTail s.rpool rpoolLen ⋆ R, by dsimp only [buildRPass2Ro]; ac_rfl⟩

theorem buildRPass2Ro_rsPool {s : ArCtxState} {ruleOff ruleN rsM : List (BitVec 32)}
    {rsL rsH : List (BitVec 64)} {rsPool : List (BitVec 32)} {flippedArr : List (BitVec 8)}
    {rmLen rpoolLen : Nat} {rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {R : Mem 64 → Prop} :
    ∃ rest, buildRPass2Ro s ruleOff ruleN rsM rsL rsH rsPool flippedArr rmLen rpoolLen
      rm2 rl2 rh2 R = (array (t := i32) s.rs_pool rsPool ⋆ rest) :=
  ⟨array (t := i32) s.rule_off ruleOff ⋆ array (t := i32) s.rule_n ruleN ⋆
    array (t := i8) s.flipped flippedArr ⋆ array (t := i32) s.rs_m rsM ⋆ array64 s.rs_l rsL ⋆
    array64 s.rs_h rsH ⋆ u32PadTail s.rs_m rsM.length ⋆
    u32PadTail s.rs_pool rsPool.length ⋆ array (t := i32) s.rm2 rm2 ⋆ array64 s.rl2 rl2 ⋆
    array64 s.rh2 rh2 ⋆ u32PadTail s.rm rmLen ⋆ u32PadTail s.rm2 rm2.length ⋆
    u32PadTail s.rpool rpoolLen ⋆ R, by dsimp only [buildRPass2Ro]; ac_rfl⟩

theorem bv32_and1_eq_zero_iff (x : BitVec 32) : (x &&& 1#32 = 0#32) ↔ x.toNat % 2 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl,
    show (0#32 : BitVec 32).toNat = 0 from rfl, Nat.and_one_is_mod]

theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [Nat.shiftRight_eq_div_pow]

theorem bv64_shl1_toNat (f : BitVec 32) (hf : f.toNat < 64) :
    (1#64 <<< f.setWidth 64).toNat = 2 ^ f.toNat := by
  have hf64 : (f.setWidth 64).toNat = f.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hpow : 2 ^ f.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hf
  rw [bv_c0_toNat_shiftLeft_bv, hf64, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.one_mul, Nat.mod_eq_of_lt hpow]

theorem bv64_shr_and1_toNat (S : BitVec 64) (fi : BitVec 32) (hfi : fi.toNat < 64) :
    ((S >>> fi.setWidth 64) &&& 1#64).toNat = (S.toNat / 2 ^ fi.toNat) % 2 := by
  have hfi64 : (fi.setWidth 64).toNat = fi.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_and, bv_c0_toNat_ushiftRight_bv, hfi64,
    show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]

theorem bv64_one_and_mlo {nOut : Nat} {mlo mhi : BitVec 64} (hm : MasksOk nOut mlo mhi) :
    (1#64 &&& mlo) = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  have h1 := hm.1
  have hk : 1 ≤ min nOut 64 := by omega
  have hlt : 2 ^ min nOut 64 - 1 < 2 ^ 64 := by
    have : 2 ^ min nOut 64 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)
    omega
  rw [BitVec.toNat_and, hm.2.2.1, maskVal64,
    show (1#64 : BitVec 64).toNat = 1 from rfl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.and_comm, Nat.and_one_is_mod]
  have hev : 2 ^ min nOut 64 = 2 * 2 ^ (min nOut 64 - 1) := by
    conv => lhs; rw [← Nat.sub_add_cancel hk, Nat.pow_succ']
  rw [hev]
  have hpos : 0 < 2 ^ (min nOut 64 - 1) := Nat.pow_pos (by decide)
  generalize 2 ^ (min nOut 64 - 1) = pow at hpos ⊢
  omega

theorem bv32_xor1_toNat (p : Nat) :
    (BitVec.ofNat 32 p ^^^ 1#32).toNat = (p % 2 ^ 32) ^^^ 1 := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, show (1#32 : BitVec 32).toNat = 1 from rfl]

theorem bv32_xor1_small (p : Nat) (hp : p < 2) :
    (BitVec.ofNat 32 p ^^^ 1#32).toNat = p ^^^ 1 := by
  rw [bv32_xor1_toNat, Nat.mod_eq_of_lt (by omega)]

theorem loadVal_arr8_idx {a base : BitVec 64} {xs : List (BitVec 8)} {i : BitVec 32}
    {R : Mem 64 → Prop} {m : Mem 64}
    (ha : a = base + BitVec.setWidth 64 i) (hi : i.toNat < xs.length)
    (hm : (array (t := i8) base xs ⋆ R) m) :
    loadVal m i8 a = some (xs[i.toNat]) := by
  have ha' : a = base + BitVec.ofNat 64 (i8.bytes * i.toNat) := by
    rw [ha]; congr 1; apply BitVec.eq_of_toNat_eq
    simp [Ty.bytes, Ty.size, BitVec.toNat_setWidth]
  rw [ha']
  exact loadVal_array (t := i8) (by decide) hi hm

theorem wp_load_arr8_idx {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a : Arg Val i64} {k : Val i8 → Expr Val Cont rs}
    {base : BitVec 64} {xs : List (BitVec 8)} {i : BitVec 32} {R : Mem 64 → Prop}
    (ha : a.val = base + BitVec.setWidth 64 i) (hi : i.toNat < xs.length)
    (hm : (array (t := i8) base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[i.toNat])) m) : wp Γ Q X (.load i8 a k) m :=
  head_wp_load rfl (loadVal_arr8_idx ha hi hm) hk

theorem wp_store_arr64_abs {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

theorem pass2_dedup_slice_ok {rpool : List (BitVec 32)} {rp mlen : Nat}
    {acc : List Nat} {x : BitVec 32}
    (hrp_len : rp + mlen + 1 ≤ rpool.length) (hacc_len : acc.length < mlen)
    (hacc_eq : ∀ p < acc.length, (rpool.getD (rp + 1 + p) 0#32).toNat = acc.getD p 0) :
    let acc' := dedupPush acc x.toNat
    let k' := acc'.length + 1
    let rpool' := if acc.getLast? = some x.toNat then rpool
      else rpool.set (rp + 1 + acc.length) x
    rpool'.length = rpool.length ∧
    k' ≤ mlen + 1 ∧
    (∀ idx < rp + 1, rpool'.getD idx 0#32 = rpool.getD idx 0#32) ∧
    (∀ p < acc'.length, (rpool'.getD (rp + 1 + p) 0#32).toNat = acc'.getD p 0) := by
  dsimp only
  dsimp only [dedupPush]
  by_cases hlast : acc.getLast? = some x.toNat
  · simp [hlast]
    exact ⟨by omega, hacc_eq⟩
  · simp only [hlast, ↓reduceIte]
    have hidx_lt : rp + 1 + acc.length < rpool.length := by omega
    refine ⟨by simp, by simp only [List.length_append, List.length_singleton]; omega,
      fun idx hidx => ?_, fun p hp => ?_⟩
    · rw [getD_set_eq rpool 0#32 x hidx_lt, ite_eq_right (by omega)]
    · simp only [List.length_append, List.length_singleton] at hp
      rw [getD_set_eq rpool 0#32 x hidx_lt]
      by_cases hpe : p = acc.length
      · subst hpe
        simp only [↓reduceIte, List.getD_eq_getElem?_getD]
        simp
      · have hplt : p < acc.length := by omega
        simp only [show rp + 1 + p ≠ rp + 1 + acc.length by omega, ↓reduceIte]
        rw [hacc_eq p hplt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hplt]

theorem pass2_finalize_slice {rpool : List (BitVec 32)} {rp mlen : Nat} {acc : List Nat}
    (hrp_len : rp + mlen + 1 ≤ rpool.length) (_hacc_len : acc.length ≤ mlen)
    (hacc32 : acc.length < 2 ^ 32)
    (hacc_eq : ∀ p < acc.length, (rpool.getD (rp + 1 + p) 0#32).toNat = acc.getD p 0) :
    let rpool' := rpool.set rp (BitVec.ofNat 32 acc.length)
    rpool'.length = rpool.length ∧
    (∀ idx < rp, rpool'.getD idx 0#32 = rpool.getD idx 0#32) ∧
    MonoSliceOk rpool' rp (rp + acc.length + 1) ∧
    (rpool'.getD rp 0#32).toNat + 1 = acc.length + 1 ∧
    symListAt rpool' rp = acc := by
  dsimp only
  have hrp_lt : rp < rpool.length := by omega
  have hlen_nat : (BitVec.ofNat 32 acc.length).toNat = acc.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hacc32]
  have hrp0 : (rpool.set rp (BitVec.ofNat 32 acc.length)).getD rp 0#32 =
      BitVec.ofNat 32 acc.length := by
    rw [getD_set_eq rpool 0#32 _ hrp_lt, ite_eq_left rfl]
  refine ⟨by simp, fun idx hidx => ?_, ⟨by omega, ?_⟩, ?_, ?_⟩
  · rw [getD_set_eq rpool 0#32 _ hrp_lt, ite_eq_right (by omega)]
  · rw [hrp0, hlen_nat]; omega
  · rw [hrp0, hlen_nat]
  · simp only [symListAt, hrp0, hlen_nat]
    apply List.ext_getElem (by simp)
    intro p hp1 hp2
    simp only [List.length_map, List.length_range] at hp1
    simp only [List.getElem_map, List.getElem_range]
    rw [getD_set_eq rpool 0#32 _ hrp_lt, ite_eq_right (by omega), hacc_eq p hp1,
      getD_eq_getElem acc 0 hp1]

theorem CombineRInv.start {nOut : Nat} {σ : Nat → Bool} {rpool rm : List (BitVec 32)}
    {rl rh : List (BitVec 64)} {aArr rm2 : List (BitVec 32)} {rl2 rh2 : List (BitVec 64)}
    {n rcap : Nat} {rm2Ptr rl2Ptr rh2Ptr : BitVec 64} {Rcmb : Mem 64 → Prop} {m : Mem 64}
    (hrm2 : rcap ≤ rm2.length) (hrl2 : rcap ≤ rl2.length) (hrh2 : rcap ≤ rh2.length)
    (hperm : PermN aArr n)
    (hm : (array (t := i32) rm2Ptr rm2 ⋆ array64 rl2Ptr rl2 ⋆
      array64 rh2Ptr rh2 ⋆ Rcmb) m) :
    CombineRInv nOut σ rpool rm rl rh aArr n rcap rm2Ptr rl2Ptr rh2Ptr Rcmb 0 0 m :=
  ⟨rm2, rl2, rh2, hrm2, hrl2, hrh2, Nat.zero_le _, Nat.zero_le _, fun _ hp => by omega,
    (by
      have h1 : polyEvalIdxOf nOut σ rpool rm rl rh aArr 0 n =
          ((List.range n).map (fun k => (aArr.getD k 0#32).toNat)).foldl
            (fun acc idx => acc + termEval nOut σ rpool rm rl rh idx) 0#nOut := by
        simp [polyEvalIdxOf, List.foldl_map]
      have h2 : polyEval nOut σ rpool rm rl rh n =
          (List.range n).foldl
            (fun acc idx => acc + termEval nOut σ rpool rm rl rh idx) 0#nOut := by
        simp [polyEval, polyEvalRange]
      simp only [polyEval_zero, Nat.sub_zero, BitVec.zero_add]
      rw [h1, h2]; exact foldl_add_perm _ hperm), hm⟩

theorem CombineRInv.step_drop {nOut : Nat} {σ : Nat → Bool} {rpool rm : List (BitVec 32)}
    {rl rh : List (BitVec 64)} {aArr : List (BitVec 32)} {n rcap k2 i j : Nat}
    {rm2Ptr rl2Ptr rh2Ptr : BitVec 64} {Rcmb : Mem 64 → Prop} {m : Mem 64}
    {h0 : BitVec 32} {l h : BitVec 64}
    (hinv : CombineRInv nOut σ rpool rm rl rh aArr n rcap rm2Ptr rl2Ptr rh2Ptr Rcmb k2 i m)
    (hij : i + 1 ≤ j) (hjn : j ≤ n)
    (hl0 : l = 0#64) (hh_0 : h = 0#64)
    (hjSum : (if monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
      polyEvalIdxOf nOut σ rpool rm rl rh aArr j (n - j) =
      polyEvalIdxOf nOut σ rpool rm rl rh aArr i (n - i)) :
    CombineRInv nOut σ rpool rm rl rh aArr n rcap rm2Ptr rl2Ptr rh2Ptr Rcmb k2 j m := by
  obtain ⟨rm2C, rl2C, rh2C, hrm2, hrl2, hrh2, hk2i, hin, hpref, hev, hm⟩ := hinv
  have hzero : (if monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
      then coeff128 nOut l h else 0#nOut) = 0#nOut := by
    subst hl0; subst hh_0; simp [coeff128]
  rw [hzero, BitVec.zero_add] at hjSum
  exact ⟨rm2C, rl2C, rh2C, hrm2, hrl2, hrh2, by omega, hjn, hpref,
    by rw [hjSum]; exact hev, hm⟩

theorem CombineRInv.step_emit {nOut : Nat} {σ : Nat → Bool} {rpool rm : List (BitVec 32)}
    {rl rh : List (BitVec 64)} {aArr : List (BitVec 32)} {n rcap k2 i j : Nat}
    {rm2Ptr rl2Ptr rh2Ptr : BitVec 64} {Rcmb : Mem 64 → Prop} {m' : Mem 64}
    {h0 : BitVec 32} {l h : BitVec 64}
    {rm2C : List (BitVec 32)} {rl2C rh2C : List (BitVec 64)}
    (hrm2 : rcap ≤ rm2C.length) (hrl2 : rcap ≤ rl2C.length) (hrh2 : rcap ≤ rh2C.length)
    (hk2i : k2 ≤ i) (hin : i < n) (hn_rcap : n ≤ rcap)
    (hh0_lt : h0.toNat < n)
    (hpref : ∀ p < k2, ∃ idx < n, rm2C.getD p 0#32 = rm.getD idx 0#32)
    (hev : polyEval nOut σ rpool rm2C rl2C rh2C k2 +
      polyEvalIdxOf nOut σ rpool rm rl rh aArr i (n - i) =
      polyEval nOut σ rpool rm rl rh n)
    (hij : i + 1 ≤ j) (hjn : j ≤ n)
    (hjSum : (if monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) +
      polyEvalIdxOf nOut σ rpool rm rl rh aArr j (n - j) =
      polyEvalIdxOf nOut σ rpool rm rl rh aArr i (n - i))
    (hstore : (array (t := i32) rm2Ptr (rm2C.set k2 (rm.getD h0.toNat 0#32)) ⋆
      array64 rl2Ptr (rl2C.set k2 l) ⋆ array64 rh2Ptr (rh2C.set k2 h) ⋆ Rcmb) m') :
    CombineRInv nOut σ rpool rm rl rh aArr n rcap rm2Ptr rl2Ptr rh2Ptr Rcmb (k2 + 1) j m' := by
  have hk2_rm2 : k2 < rm2C.length := by omega
  have hk2_rl2 : k2 < rl2C.length := by omega
  have hk2_rh2 : k2 < rh2C.length := by omega
  let rm2' := rm2C.set k2 (rm.getD h0.toNat 0#32)
  let rl2' := rl2C.set k2 l
  let rh2' := rh2C.set k2 h
  have hkeep : ∀ t ≤ k2, polyEval nOut σ rpool rm2' rl2' rh2' t =
      polyEval nOut σ rpool rm2C rl2C rh2C t := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      have hne : t ≠ k2 := by omega
      rw [polyEval_succ, polyEval_succ, ih (by omega)]
      congr 1
      simp only [termEval, rm2', rl2', rh2', getD_set_eq _ 0#32 _ hk2_rm2,
        getD_set_eq _ 0#64 _ hk2_rl2, getD_set_eq _ 0#64 _ hk2_rh2, ite_eq_right hne]
  have hterm : termEval nOut σ rpool rm2' rl2' rh2' k2 =
      (if monoValL σ (symListAt rpool (rm.getD h0.toNat 0#32).toNat)
        then coeff128 nOut l h else 0#nOut) := by
    simp only [termEval, rm2', rl2', rh2', getD_set_eq _ 0#32 _ hk2_rm2,
      getD_set_eq _ 0#64 _ hk2_rl2, getD_set_eq _ 0#64 _ hk2_rh2, ↓reduceIte]
  refine ⟨rm2', rl2', rh2', by simpa [rm2'], by simpa [rl2'], by simpa [rh2'], by omega, hjn,
    fun p hp => ?_, ?_, hstore⟩
  · by_cases hpk : p = k2
    · subst hpk
      exact ⟨h0.toNat, hh0_lt, by simp only [rm2', getD_set_eq _ 0#32 _ hk2_rm2, ↓reduceIte]⟩
    · obtain ⟨idx, hidx, hEq⟩ := hpref p (by omega)
      exact ⟨idx, hidx, by
        simp only [rm2', getD_set_eq _ 0#32 _ hk2_rm2, ite_eq_right hpk, hEq]⟩
  · rw [polyEval_succ, hkeep k2 (le_refl _), hterm, BitVec.add_assoc, hjSum]
    exact hev

end

/-! ## 3. Pass 2 AST Matchers & `buildR_pass2_wp` (`ar_build_R`) -/

public section

@[expose] def buildRPass2EntryExpr (cx : Val i64) (v off cnt : Val i32) (fv_b any : Val .bool)
    (bt bw : Val i64) : Expr Val Cont [.bool] :=
  match ar_build_R_body Val Cont (cx, v, ()) with
  | @Expr.let_ _ _ _ [.bits 64] _ r0 => match r0 (0#64, ()) with
    | @Expr.load _ _ _ (.bits 64) _ r1 => match r1 0#64 with
      | @Expr.let_ _ _ _ [.bits 64] _ r2 => match r2 (0#64, ()) with
        | @Expr.let_ _ _ _ [.bits 64] _ r3 => match r3 (0#64, ()) with
          | @Expr.let_ _ _ _ [.bits 64] _ r4 => match r4 (0#64, ()) with
            | @Expr.load _ _ _ (.bits 32) _ r5 => match r5 off with
              | @Expr.let_ _ _ _ [.bits 64] _ r6 => match r6 (0#64, ()) with
                | @Expr.load _ _ _ (.bits 64) _ r7 => match r7 0#64 with
                  | @Expr.let_ _ _ _ [.bits 64] _ r8 => match r8 (0#64, ()) with
                    | @Expr.let_ _ _ _ [.bits 64] _ r9 => match r9 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ r10 => match r10 (0#64, ()) with
                        | @Expr.load _ _ _ (.bits 32) _ r11 => match r11 cnt with
                          | @Expr.let_ _ _ _ [.bits 64] _ r12 => match r12 (0#64, ()) with
                            | @Expr.load _ _ _ (.bits 64) _ r13 => match r13 0#64 with
                              | @Expr.let_ _ _ _ [.bits 64] _ r14 => match r14 (0#64, ()) with
                                | @Expr.let_ _ _ _ [.bits 64] _ r15 => match r15 (0#64, ()) with
                                  | @Expr.load _ _ _ (.bits 8) _ r16 => match r16 0#8 with
                                    | @Expr.let_ _ _ _ [.bits 8] _ r17 => (match r17 (0#8, ()) with
    | @Expr.let_ _ _ _ [.bits 32] _ r18 => match r18 (0#32, ()) with
      | @Expr.let_ _ _ _ [.bits 32] _ r19 => match r19 (0#32, ()) with
        | @Expr.let_ _ _ _ [.bool] _ r20 => match r20 (fv_b, ()) with
          | @Expr.group _ _ _ [[.bits 64]] bs21 _ =>
            match bs21 (fun _ _ => False, ()) with
            | .cons b21 _ => match b21 (bw, ()) with
              | @Expr.group _ _ _ [[.bits 64]] bs22 _ =>
                match bs22 (fun _ _ => False, ()) with
                | .cons b22 _ => match b22 (bt, ()) with
                  | @Expr.group _ _ _
                      [[.bool, .bits 64, .bits 64, .bits 32]]
                      bs23 _ =>
                    match bs23 (fun _ _ => False, ()) with
                    | .cons b23 _ =>
                      match b23 (any, bt, bw, cnt, ()) with
                      | @Expr.let_ _ _ _ [.bool] _ r24 =>
                        match r24 (false, ()) with
                        | .jnz _ _ eNF => match eNF with
                          | @Expr.group _ _ _ [[]] bsNF _ =>
                            match bsNF (fun _ _ => False, ()) with
                            | .cons bNF _ => bNF ()
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
    | _ => .ret (Arg.imm false, ()))
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
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

@[expose] def buildRPass2P2Exit (Ji : Cont [.bits 32, .bits 64, .bits 32]) (cx : Val i64)
    (v off cnt : Val i32) (fv_b any : Val .bool) (bt bw : Val i64) (iC : Val i32)
    (rpC : Val i64) (nC : Val i32) : Expr Val Cont [.bool] × Expr Val Cont [.bool] :=
  match buildRPass2EntryExpr cx v off cnt fv_b any bt bw with
  | @Expr.let_ _ _ _ [.bits 64] _ n0 => match n0 (0#64, ()) with
    | @Expr.load _ _ _ (.bits 32) _ n1 => match n1 0#32 with
      | @Expr.let_ _ _ _ [.bits 64] _ n2 => match n2 (0#64, ()) with
        | @Expr.let_ _ _ _ [.bool] _ n3 => match n3 (false, ()) with
          | .jnz _ _ nf1 => match nf1 with
            | @Expr.let_ _ _ _ [.bits 64] _ n4 => match n4 (0#64, ()) with
              | @Expr.load _ _ _ (.bits 32) _ n5 => match n5 0#32 with
                | @Expr.let_ _ _ _ [.bits 64] _ n6 => match n6 (0#64, ()) with
                  | @Expr.let_ _ _ _ [.bool] _ n7 => match n7 (false, ()) with
                    | .jnz _ _ nf2 => match nf2 with
                      | @Expr.let_ _ _ _ [.bits 64] _ n8 => match n8 (0#64, ()) with
                        | @Expr.load _ _ _ (.bits 64) _ n9 => match n9 0#64 with
                          | @Expr.let_ _ _ _ [.bool] _ n10 => match n10 (false, ()) with
                            | .jnz _ _ nf3 => match nf3 with
                              | @Expr.group _ _ _ [[.bits 64, .bits 32]] bsInit _ =>
                                match bsInit (fun _ _ => False, ()) with
                                | .cons bInit _ => match bInit (0#64, 0#32, ()) with
                                  | @Expr.group _ _ _ [[.bits 32, .bits 64, .bits 32]] bsP2 _ =>
                                    match bsP2 (Ji, ()) with
                                    | .cons bP2 _ => match bP2 (iC, rpC, nC, ()) with
                                      | @Expr.let_ _ _ _ [.bool] _ p2c => match p2c (false, ()) with
                                        | .jnz _ eLoop eAfter => (eLoop, eAfter)
                                        | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                                      | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                                    | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                                  | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                                | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                              | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                            | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                          | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                        | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                      | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                    | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                  | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
                | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
              | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
            | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
          | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
        | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
      | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
    | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
  | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))

@[expose] def buildRPass2AfterExpr (cx ixPtr ix2Ptr : Val i64) (v off cnt : Val i32)
    (fv_b any : Val .bool) (bt bw : Val i64) (nFinal : Val i32) : Expr Val Cont [.bool] :=
  match (buildRPass2P2Exit (fun _ _ => False) cx v off cnt fv_b any bt bw cnt 0#64 nFinal).2 with
  | @Expr.let_ _ _ _ [.bits 64] _ a0 => match a0 (0#64, ()) with
    | @Expr.load _ _ _ (.bits 64) _ a1 => match a1 ixPtr with
      | @Expr.let_ _ _ _ [.bits 64] _ a2 => match a2 (0#64, ()) with
        | @Expr.load _ _ _ (.bits 64) _ a3 => a3 ix2Ptr
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

@[expose] def buildRPass2SExpr (Ji : Cont [.bits 32, .bits 64, .bits 32])
    (cx rsPoolPtr mPtr nSBv : Val i64) (v off cnt : Val i32) (fv_b any : Val .bool)
    (bt bw : Val i64) (iC : Val i32) (rpC : Val i64) (nC mOffBv mlenBv : Val i32)
    (cl ch : Val i64) (fF jF : Val i32) : Expr Val Cont [.bool] :=
  match (buildRPass2P2Exit Ji cx v off cnt fv_b any bt bw iC rpC nC).1 with
  | @Expr.let_ _ _ _ [.bits 64] _ e0 => match e0 (0#64, ()) with
    | @Expr.load _ _ _ (.bits 64) _ e1 => match e1 rsPoolPtr with
      | @Expr.let_ _ _ _ [.bits 64] _ e2 => match e2 (0#64, ()) with
        | @Expr.load _ _ _ (.bits 64) _ e3 => match e3 0#64 with
          | @Expr.let_ _ _ _ [.bits 32] _ e4 => match e4 (0#32, ()) with
            | @Expr.let_ _ _ _ [.bits 64] _ e5 => match e5 (0#64, ()) with
              | @Expr.let_ _ _ _ [.bits 64] _ e6 => match e6 (0#64, ()) with
                | @Expr.let_ _ _ _ [.bits 64] _ e7 => match e7 (0#64, ()) with
                  | @Expr.load _ _ _ (.bits 32) _ e8 => match e8 mOffBv with
                    | @Expr.let_ _ _ _ [.bits 64] _ e9 => match e9 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ e10 => match e10 (0#64, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ e11 => match e11 (mPtr, ()) with
                          | @Expr.let_ _ _ _ [.bits 64] _ e11b => match e11b (0#64, ()) with
                            | @Expr.let_ _ _ _ [.bits 64] _ e11c => match e11c (0#64, ()) with
                              | @Expr.let_ _ _ _ [.bits 64] _ e11d => match e11d (0#64, ()) with
                                | @Expr.load _ _ _ (.bits 32) _ e12 => match e12 mlenBv with
                                  | @Expr.let_ _ _ _ [.bits 64] _ e13 => match e13 (0#64, ()) with
                                    | @Expr.load _ _ _ (.bits 64) _ e14 => (match e14 0#64 with
    | @Expr.let_ _ _ _ [.bits 32] _ e15 => match e15 (0#32, ()) with
      | @Expr.let_ _ _ _ [.bits 64] _ e16 => match e16 (0#64, ()) with
        | @Expr.let_ _ _ _ [.bits 64] _ e17 => match e17 (0#64, ()) with
          | @Expr.let_ _ _ _ [.bits 64] _ e17b => match e17b (0#64, ()) with
            | @Expr.load _ _ _ (.bits 64) _ e18 => match e18 cl with
              | @Expr.let_ _ _ _ [.bits 64] _ e19 => match e19 (0#64, ()) with
                | @Expr.load _ _ _ (.bits 64) _ e20 => match e20 0#64 with
                  | @Expr.let_ _ _ _ [.bits 32] _ e21 => match e21 (0#32, ()) with
                    | @Expr.let_ _ _ _ [.bits 64] _ e22 => match e22 (0#64, ()) with
                      | @Expr.let_ _ _ _ [.bits 64] _ e23 => match e23 (0#64, ()) with
                        | @Expr.let_ _ _ _ [.bits 64] _ e23b => match e23b (0#64, ()) with
                          | @Expr.load _ _ _ (.bits 64) _ e24 => match e24 ch with
                            | @Expr.group _ _ _ [[.bits 32, .bits 32]] bsF _ =>
                              match bsF (fun _ _ => False, ()) with
                              | .cons bF _ => match bF (fF, jF, ()) with
                                | @Expr.let_ _ _ _ [.bool] _ fc => match fc (false, ()) with
                                  | .jnz _ _ eSPre => match eSPre with
                                    | @Expr.let_ _ _ _ [.bits 64] _ s0 => match s0 (0#64, ()) with
                                      | @Expr.let_ _ _ _ [.bits 64] _ s1 => s1 (nSBv, ())
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
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ()))
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
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

@[expose] def buildRPass2SBranches (Ji : Cont [.bits 32, .bits 64, .bits 32])
    (Js : Cont [.bits 64, .bits 32, .bits 32, .bits 64]) (cx rsPoolPtr mPtr nSBv : Val i64)
    (v off cnt : Val i32) (fv_b any : Val .bool) (bt bw : Val i64) (iC : Val i32)
    (rpC : Val i64) (nC mOffBv mlenBv : Val i32) (cl ch : Val i64) (fF jF : Val i32)
    (rpS : Val i64) (nS_cur jU : Val i32) (S : Val i64) :
    Expr Val Cont [.bool] × Expr Val Cont [.bool] :=
  match buildRPass2SExpr Ji cx rsPoolPtr mPtr nSBv v off cnt fv_b any bt bw iC rpC nC mOffBv
      mlenBv cl ch fF jF with
  | @Expr.group _ _ _ [[.bits 64, .bits 32, .bits 32, .bits 64]] bsS _ =>
    match bsS (Js, ()) with
    | .cons bS _ => match bS (rpS, nS_cur, jU, S, ()) with
      | @Expr.let_ _ _ _ [.bool] _ sc => match sc (false, ()) with
        | .jnz _ eSBody eSAfter => (eSBody, eSAfter)
        | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
      | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
    | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))
  | _ => (.ret (Arg.imm false, ()), .ret (Arg.imm false, ()))

@[expose] def buildRPass2JExpr (Ji : Cont [.bits 32, .bits 64, .bits 32])
    (Js : Cont [.bits 64, .bits 32, .bits 32, .bits 64])
    (cx rsPoolPtr mPtr nSBv rpoolPtr outPtr : Val i64) (v off cnt : Val i32)
    (fv_b any : Val .bool) (bt bw : Val i64) (iC : Val i32) (rpC : Val i64)
    (nC mOffBv mlenBv : Val i32) (cl ch : Val i64) (fF jF : Val i32)
    (rpS : Val i64) (nS_cur jU : Val i32) (S : Val i64) : Expr Val Cont [.bool] :=
  match (buildRPass2SBranches Ji Js cx rsPoolPtr mPtr nSBv v off cnt fv_b any bt bw iC rpC nC
      mOffBv mlenBv cl ch fF jF rpS nS_cur jU S).1 with
  | @Expr.let_ _ _ _ [.bits 64] _ j0 => match j0 (0#64, ()) with
    | @Expr.load _ _ _ (.bits 64) _ j1 => match j1 rpoolPtr with
      | @Expr.let_ _ _ _ [.bits 64] _ j2 => match j2 (0#64, ()) with
        | @Expr.let_ _ _ _ [.bits 64] _ j3 => j3 (outPtr, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

@[expose] def buildRPass2JAfterExpr (Ji : Cont [.bits 32, .bits 64, .bits 32])
    (Js : Cont [.bits 64, .bits 32, .bits 32, .bits 64])
    (cx rsPoolPtr mPtr nSBv rpoolPtr outPtr : Val i64) (v off cnt : Val i32)
    (fv_b any : Val .bool) (bt bw : Val i64) (iC : Val i32) (rpC : Val i64)
    (nC mOffBv mlenBv : Val i32) (cl ch : Val i64) (fF jF : Val i32)
    (rpS : Val i64) (nS_cur jU : Val i32) (S : Val i64)
    (jJ kJ fiJ parJ : Val i32) : Expr Val Cont [.bool] :=
  match buildRPass2JExpr Ji Js cx rsPoolPtr mPtr nSBv rpoolPtr outPtr v off cnt fv_b any bt bw
      iC rpC nC mOffBv mlenBv cl ch fF jF rpS nS_cur jU S with
  | @Expr.group _ _ _ [[.bits 32, .bits 32, .bits 32, .bits 32]] bsJ _ =>
    match bsJ (fun _ _ => False, ()) with
    | .cons bJ _ => match bJ (jJ, kJ, fiJ, parJ, ()) with
      | @Expr.let_ _ _ _ [.bool] _ jc => match jc (false, ()) with
        | .jnz _ _ eJAfter => match eJAfter with
          | @Expr.let_ _ _ _ [.bits 64] _ ja0 =>
            match ja0 (BitVec.signExtend 64 0#32, ()) with
            | @Expr.let_ _ _ _ [.bits 64] _ ja1 => match ja1 (0#64, ()) with
              | @Expr.let_ _ _ _ [.bits 64] _ ja2 =>
                match ja2 (outPtr + BitVec.ofNat 64 0 * 4, ()) with
                | @Expr.let_ _ _ _ [.bits 32] _ ja3 => ja3 (kJ - 1#32, ())
                | _ => .ret (Arg.imm false, ())
              | _ => .ret (Arg.imm false, ())
            | _ => .ret (Arg.imm false, ())
          | _ => .ret (Arg.imm false, ())
        | _ => .ret (Arg.imm false, ())
      | _ => .ret (Arg.imm false, ())
    | _ => .ret (Arg.imm false, ())
  | _ => .ret (Arg.imm false, ())

private theorem arr32_add_idx_addr (base off64 : BitVec 64) (idx : BitVec 32) :
    base + off64 * 4 + BitVec.setWidth 64 idx * 4 =
      base + BitVec.ofNat 64 (4 * (off64.toNat + idx.toNat)) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, Nat.mul_add, Nat.mul_comm _ 4]

theorem wp_load_arr32_add {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    {base off64 : BitVec 64} {xs : List (BitVec 32)} {idx : BitVec 32} {R : Mem 64 → Prop}
    (ha : a.val = base + off64 * 4 + BitVec.setWidth 64 idx * 4)
    (hi : off64.toNat + idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : wp Γ Q X (k (xs[off64.toNat + idx.toNat])) m) : wp Γ Q X (.load i32 a k) m := by
  rw [arr32_add_idx_addr] at ha
  exact head_wp_load ha (loadVal_array (t := i32) (by decide) hi hm) hk

theorem wp_store_arr32_add {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {v : Arg Val i32} {a : Arg Val i64} {val : BitVec 32} {k : Expr Val Cont rs}
    {base off64 : BitVec 64} {xs : List (BitVec 32)} {idx : BitVec 32} {R : Mem 64 → Prop}
    (hv : v.val = val) (ha : a.val = base + off64 * 4 + BitVec.setWidth 64 idx * 4)
    (hi : off64.toNat + idx.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : ∀ m', (array (t := i32) base (xs.set (off64.toNat + idx.toNat) val) ⋆ R) m' →
      wp Γ Q X k m') : wp Γ Q X (.store v a k) m := by
  rw [arr32_add_idx_addr] at ha
  exact head_wp_store hv ha (store_array (t := i32) val (by decide) hi hm) hk

theorem wp_store_arr32_add0 {Γ : T.Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {v : Arg Val i32} {a : Arg Val i64} {val : BitVec 32} {k : Expr Val Cont rs}
    {base off64 : BitVec 64} {xs : List (BitVec 32)} {R : Mem 64 → Prop}
    (hv : v.val = val) (ha : a.val = base + off64 * 4 + BitVec.signExtend 64 0#32 * 4)
    (hi : off64.toNat < xs.length) (hm : (array (t := i32) base xs ⋆ R) m)
    (hk : ∀ m', (array (t := i32) base (xs.set off64.toNat val) ⋆ R) m' →
      wp Γ Q X k m') : wp Γ Q X (.store v a k) m := by
  have ha' : a.val = base + BitVec.ofNat 64 (4 * off64.toNat) := by
    have hz : BitVec.signExtend 64 0#32 = 0#64 := by decide
    rw [ha, hz, BitVec.zero_mul, BitVec.add_zero]
    congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_comm off64.toNat 4]
  exact head_wp_store hv ha' (store_array (t := i32) val (by decide) hi hm) hk

theorem expandFold_par_xor (flippedArr : List (BitVec 8)) (S : Nat)
    (xs acc : List Nat) (fi par b : Nat) :
    let r1 := xs.foldl (expandStep flippedArr S) (acc, fi, par ^^^ b)
    let r2 := xs.foldl (expandStep flippedArr S) (acc, fi, par)
    r1.1 = r2.1 ∧ r1.2.1 = r2.2.1 ∧ r1.2.2 = r2.2.2 ^^^ b := by
  induction xs generalizing acc fi par with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons, expandStep]
    split
    · split
      · exact ih acc (fi + 1) par
      · have h := ih (dedupPush acc (x + 1)) (fi + 1) (par ^^^ 1)
        have hx : (par ^^^ b) ^^^ 1 = (par ^^^ 1) ^^^ b := by
          rw [Nat.xor_assoc, Nat.xor_comm b 1, ← Nat.xor_assoc]
        rwa [hx]
    · exact ih (dedupPush acc x) fi par

private theorem expandFold_pairwise_aux (flippedArr : List (BitVec 8)) (S fi par : Nat) :
    ∀ (xs acc : List Nat),
      xs.Pairwise (· < ·) → acc.Pairwise (· < ·) →
      (∀ a ∈ acc, ∀ x ∈ xs, a ≤ x) →
      (∀ a ∈ acc, ∀ x ∈ xs, a = x → x % 2 = 1) →
      (xs.foldl (expandStep flippedArr S) (acc, fi, par)).1.Pairwise (· < ·)
  | [], acc, _, hacc, _, _ => hacc
  | x :: xs, acc, hxs, hacc, hle, hodd => by
    rw [List.pairwise_cons] at hxs
    have hacc_x : ∀ a ∈ acc, a ≤ x := fun a ha => hle a ha x (by simp)
    have hacc_odd : ∀ a ∈ acc, a = x → x % 2 = 1 := fun a ha heq => hodd a ha x (by simp) heq
    have hpush_lt : ∀ (acc0 : List Nat) (z : Nat),
        acc0.Pairwise (· < ·) → (∀ a ∈ acc0, a < z) →
        (dedupPush acc0 z).Pairwise (· < ·) := fun acc0 z hp0 hlt => by
      dsimp only [dedupPush]
      split
      · exact hp0
      · exact List.pairwise_append.mpr ⟨hp0, List.pairwise_singleton _ _, fun a ha b hb => by
          rw [List.mem_singleton] at hb; subst hb; exact hlt a ha⟩
    have hpush_mem : ∀ (acc0 : List Nat) (z a : Nat),
        a ∈ dedupPush acc0 z → a ∈ acc0 ∨ a = z := fun acc0 z a ha => by
      dsimp only [dedupPush] at ha
      split at ha
      · exact Or.inl ha
      · simp only [List.mem_append, List.mem_singleton] at ha; exact ha
    simp only [List.foldl_cons, expandStep]
    split
    · next hfc =>
      have hx0 : x % 2 = 0 := by
        simp only [flipCond, Bool.and_eq_true, beq_iff_eq] at hfc; exact hfc.1
      have hacc_lt : ∀ a ∈ acc, a < x := fun a ha =>
        Nat.lt_of_le_of_ne (hacc_x a ha) (fun heq => by have := hacc_odd a ha heq; omega)
      split
      · refine expandFold_pairwise_aux flippedArr S (fi + 1) par xs acc hxs.2 hacc ?_ ?_
        · intro a ha y hy; exact Nat.le_of_lt (lt_trans (hacc_lt a ha) (hxs.1 y hy))
        · intro a ha y hy heq; have := lt_trans (hacc_lt a ha) (hxs.1 y hy); omega
      · refine expandFold_pairwise_aux flippedArr S (fi + 1) (par ^^^ 1) xs
          (dedupPush acc (x + 1)) hxs.2
          (hpush_lt acc (x + 1) hacc (fun a ha => by have := hacc_lt a ha; omega)) ?_ ?_
        · intro a ha y hy
          rcases hpush_mem acc (x + 1) a ha with ha0 | rfl
          · exact Nat.le_of_lt (lt_trans (hacc_lt a ha0) (hxs.1 y hy))
          · exact hxs.1 y hy
        · intro a ha y hy heq
          rcases hpush_mem acc (x + 1) a ha with ha0 | rfl
          · have := lt_trans (hacc_lt a ha0) (hxs.1 y hy); omega
          · rw [← heq]; omega
    · refine expandFold_pairwise_aux flippedArr S fi par xs (dedupPush acc x) hxs.2 ?_ ?_ ?_
      · dsimp only [dedupPush]
        split
        · exact hacc
        · rename_i hne
          refine List.pairwise_append.mpr ⟨hacc, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb; subst hb
          refine Nat.lt_of_le_of_ne (hacc_x a ha) fun hax => ?_
          subst hax
          cases hlast : acc.getLast? with
          | none =>
            have hne_nil := List.ne_nil_of_mem ha
            exact absurd (List.getLast?_eq_none_iff.mp hlast) hne_nil
          | some g =>
            have hg_mem := List.mem_of_getLast? hlast
            have hga := hacc_x g hg_mem
            have hlen_pos : 0 < acc.length := List.length_pos_of_mem ha
            have ha_lt_or : a = g ∨ a < g := by
              rw [List.getLast?_eq_some_iff] at hlast
              obtain ⟨ys, hys⟩ := hlast
              rw [hys] at ha hacc
              rw [List.mem_append, List.mem_singleton] at ha
              rcases ha with ha | rfl
              · right; exact (List.pairwise_append.mp hacc).2.2 a ha g (by simp)
              · left; rfl
            rcases ha_lt_or with rfl | hlt
            · exact hne hlast
            · omega
      · intro a ha y hy
        rcases hpush_mem acc x a ha with ha0 | rfl
        · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hacc_x a ha0) (hxs.1 y hy))
        · exact Nat.le_of_lt (hxs.1 y hy)
      · intro a ha y hy heq
        rcases hpush_mem acc x a ha with ha0 | rfl
        · have := lt_of_le_of_lt (hacc_x a ha0) (hxs.1 y hy); omega
        · have := hxs.1 y hy; omega

theorem expandFold_pairwise (flippedArr : List (BitVec 8)) (S fi par : Nat) (xs : List Nat)
    (hxs : xs.Pairwise (· < ·)) :
    (xs.foldl (expandStep flippedArr S) ([], fi, par)).1.Pairwise (· < ·) :=
  expandFold_pairwise_aux flippedArr S fi par xs [] hxs (List.Pairwise.nil)
    (fun _ h => by cases h) (fun _ h => by cases h)

theorem pass2_S_done_inv {nOut bd : Nat} (flippedArr : List (BitVec 8))
    {rsPool : List (BitVec 32)} {mOff mlen S : Nat} {fv_b : Bool}
    {rpool0 rpool1 rmS : List (BitVec 32)} {rlS rhS : List (BitVec 64)}
    {rpS nS : Nat} {cl ch lFin hFin : BitVec 64}
    (hxs : ∀ x ∈ symListAt rsPool mOff, x / 2 < bd)
    (hxsSorted : MonoSorted rsPool mOff)
    (hmlen : mlen = (rsPool.getD mOff 0#32).toNat)
    (hrpS_len : rpS + mlen + 1 ≤ rpool0.length)
    (hrpS_bd : rpS + mlen + 1 < 2 ^ 32)
    (hnS_len : nS < rmS.length) (hnS_rl : nS < rlS.length) (hnS_rh : nS < rhS.length)
    (hSl0 : ∀ r < nS, MonoSliceOk rpool0 (rmS.getD r 0#32).toNat rpS ∧
      (rpool0.getD (rmS.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32)
    (hSorted0 : ∀ r < nS, MonoSorted rpool0 (rmS.getD r 0#32).toNat)
    (hW0 : monoTotalWords rpool0 rmS nS = rpS)
    (hSb0 : SymsBound rpool0 rmS nS bd)
    (hacc_len : (symListAt rsPool mOff |>.foldl (expandStep flippedArr S) ([], 0, 0)).1.length ≤
      mlen)
    (hacc_eq : ∀ p < (symListAt rsPool mOff |>.foldl
        (expandStep flippedArr S) ([], 0, 0)).1.length,
      (rpool0.getD (rpS + 1 + p) 0#32).toNat =
        (symListAt rsPool mOff |>.foldl (expandStep flippedArr S) ([], 0, 0)).1.getD p 0)
    (hrpool1 : rpool1 = rpool0.set rpS (BitVec.ofNat 32
      (symListAt rsPool mOff |>.foldl (expandStep flippedArr S) ([], 0, 0)).1.length))
    (hCoeff : coeff128 nOut lFin hFin =
      if ((symListAt rsPool mOff |>.foldl (expandStep flippedArr S) ([], 0, 0)).2.2 ^^^
          (if fv_b then 1 else 0)) % 2 = 1 then
        -coeff128 nOut cl ch
      else coeff128 nOut cl ch) :
    let acc := (symListAt rsPool mOff |>.foldl (expandStep flippedArr S) ([], 0, 0)).1
    let rmS' := rmS.set nS (BitVec.ofNat 32 rpS)
    let rlS' := rlS.set nS lFin
    let rhS' := rhS.set nS hFin
    let rpS' := rpS + acc.length + 1
    rpool1.length = rpool0.length ∧
    rpS' ≤ rpS + (mlen + 1) ∧
    (∀ r < nS + 1, MonoSliceOk rpool1 (rmS'.getD r 0#32).toNat rpS' ∧
      (rpool1.getD (rmS'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32) ∧
    (∀ r < nS + 1, MonoSorted rpool1 (rmS'.getD r 0#32).toNat) ∧
    monoTotalWords rpool1 rmS' (nS + 1) = rpS' ∧
    SymsBound rpool1 rmS' (nS + 1) bd ∧
    (∀ (σ : Nat → Bool),
      polyEval nOut σ rpool1 rmS' rlS' rhS' (nS + 1) =
        polyEval nOut σ rpool0 rmS rlS rhS nS +
          expandTermEval nOut σ flippedArr (coeff128 nOut cl ch) S [] 0
            (if fv_b then 1 else 0) (symListAt rsPool mOff)) := by
  dsimp only
  have hfin := pass2_finalize_slice hrpS_len hacc_len (by omega) hacc_eq
  rw [← hrpool1] at hfin
  obtain ⟨hplen, hpref, hms_new, hword_new, hsym_new⟩ := hfin
  let rmS' := rmS.set nS (BitVec.ofNat 32 rpS)
  let rlS' := rlS.set nS lFin
  let rhS' := rhS.set nS hFin
  let rpS' := rpS +
    (symListAt rsPool mOff |>.foldl (expandStep flippedArr S) ([], 0, 0)).1.length + 1
  have hrpS_nat : (BitVec.ofNat 32 rpS).toNat = rpS := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrm_nS : (rmS'.getD nS 0#32).toNat = rpS := by
    dsimp only [rmS']; rw [getD_set_eq rmS 0#32 _ hnS_len, ite_eq_left rfl, hrpS_nat]
  have hrm_lt : ∀ r < nS, rmS'.getD r 0#32 = rmS.getD r 0#32 := by
    intro r hr; dsimp only [rmS']; rw [getD_set_eq rmS 0#32 _ hnS_len, ite_eq_right (by omega)]
  have hsy_old : ∀ r < nS,
      symListAt rpool1 (rmS'.getD r 0#32).toNat = symListAt rpool0 (rmS.getD r 0#32).toNat := by
    intro r hr
    have h1 := (hSl0 r hr).1
    rw [hrm_lt r hr]
    simp only [symListAt, hpref _ h1.1]
    apply List.map_congr_left
    intro p hp
    have hplt := List.mem_range.mp hp
    have h12 := h1.2
    rw [hpref _ (by omega)]
  have hSl' : ∀ r < nS + 1, MonoSliceOk rpool1 (rmS'.getD r 0#32).toNat rpS' ∧
      (rpool1.getD (rmS'.getD r 0#32).toNat 0#32).toNat + 1 < 2 ^ 32 := by
    intro r hr
    by_cases hrn : r = nS
    · subst hrn; rw [hrm_nS]; exact ⟨hms_new, by rw [hword_new]; omega⟩
    · have hrlt : r < nS := by omega
      obtain ⟨h1, h2⟩ := hSl0 r hrlt
      dsimp only [MonoSliceOk] at h1 ⊢
      rw [hrm_lt r hrlt, hpref _ h1.1]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  have hSorted' : ∀ r < nS + 1, MonoSorted rpool1 (rmS'.getD r 0#32).toNat := by
    intro r hr
    by_cases hrn : r = nS
    · subst hrn; rw [hrm_nS, MonoSorted, hsym_new]
      exact expandFold_pairwise flippedArr S 0 0 _ hxsSorted
    · have hrlt : r < nS := by omega
      exact monoSorted_congr (hsy_old r hrlt).symm (hSorted0 r hrlt)
  have hW_pref : monoTotalWords rpool1 rmS' nS = monoTotalWords rpool0 rmS nS :=
    monoTotalWords_congr_prefix (fun r hr => (hSl0 r hr).1) hpref (fun r hr => hrm_lt r hr)
  refine ⟨hplen, by omega, hSl', hSorted', ?_, fun r hr x hx => ?_, fun σ => ?_⟩
  · rw [monoTotalWords_succ, hW_pref, hW0, hrm_nS, hword_new]; omega
  · by_cases hrn : r = nS
    · subst hrn; rw [hrm_nS, hsym_new] at hx
      exact expandFold_symsBound flippedArr S bd (symListAt rsPool mOff) [] 0 0
        (fun _ hz => by cases hz) hxs x hx
    · have hrlt : r < nS := by omega
      rw [hsy_old r hrlt] at hx
      exact hSb0 r hrlt x hx
  · rw [polyEval_succ]
    have hpe_pref : polyEval nOut σ rpool1 rmS' rlS' rhS' nS =
        polyEval nOut σ rpool0 rmS rlS rhS nS := by
      apply polyEval_congr_prefix nOut σ (fun r hr => (hSl0 r hr).1) hpref
      intro r hr
      have hne : r ≠ nS := by omega
      exact ⟨hrm_lt r hr,
        by dsimp only [rlS']; rw [getD_set_eq rlS 0#64 _ hnS_rl, ite_eq_right hne],
        by dsimp only [rhS']; rw [getD_set_eq rhS 0#64 _ hnS_rh, ite_eq_right hne]⟩
    rw [hpe_pref]
    congr 1
    have hxor := expandFold_par_xor flippedArr S (symListAt rsPool mOff) [] 0 0
      (if fv_b then 1 else 0)
    have hrl_nS : rlS'.getD nS 0#64 = lFin := by
      dsimp only [rlS']; rw [getD_set_eq rlS 0#64 _ hnS_rl, ite_eq_left rfl]
    have hrh_nS : rhS'.getD nS 0#64 = hFin := by
      dsimp only [rhS']; rw [getD_set_eq rhS 0#64 _ hnS_rh, ite_eq_left rfl]
    dsimp only [rmS', rlS', rhS'] at hrm_nS hrl_nS hrh_nS
    simp only [termEval, expandTermEval, Nat.zero_xor] at hxor ⊢
    rw [hrm_nS, hsym_new, hrl_nS, hrh_nS, hxor.1, hxor.2.2, hCoeff]

theorem symListAt_take_succ {pool : List (BitVec 32)} {off j : Nat}
    (hj1 : 1 ≤ j) (hjle : j ≤ (pool.getD off 0#32).toNat) :
    (symListAt pool off).take j =
      (symListAt pool off).take (j - 1) ++ [(pool.getD (off + j) 0#32).toNat] := by
  have hlt : j - 1 < (symListAt pool off).length := by
    simp only [symListAt, List.length_map, List.length_range]; omega
  rw [show j = (j - 1) + 1 by omega, List.take_succ_eq_append_getElem hlt]
  congr 2
  simp only [symListAt, List.getElem_map, List.getElem_range]
  congr 2; omega
end

end LeanQbe.T.Examples.Arisca.Proof

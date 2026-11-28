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
# ARiSCA `ar_apply` Pure Algebra, Bounds & Focus Helpers (`Arisca.Proof.Poly2ApplyBase`)

Pure substitution identities, `bx`/`R` word-sum overflow bounds, vanishing-pair conflict
lemmas, and `tMem`/`qMem`/`pool` splitting helpers supporting `ar_apply_wp` (`Arisca.Proof.Poly2`).
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

/-! ## 1. Pure `bx` / `R` Sums & Substitution Algebra -/

@[expose] public section

/-- Sum of `termEval` over the `nb` selected term indices `bx[0..nb)`. -/
def bxTermSum (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) (nb : Nat) : BitVec nOut :=
  (List.range nb).foldl
    (fun acc b => acc + termEval nOut σ pool tm tl th (bx.getD b 0#32).toNat) 0#nOut

/-- Sum of monomial lengths `pool[tm[bx[b]]]` over `b < nb`. -/
def bxSymLenSum (pool tm bx : List (BitVec 32)) (nb : Nat) : Nat :=
  (List.range nb).foldl
    (fun acc b =>
      acc + (pool.getD (tm.getD (bx.getD b 0#32).toNat 0#32).toNat 0#32).toNat) 0

/-- Sum of monomial lengths `rp[rm[r]]` over `r < nR`. -/
def rSymLenSum (rp rm : List (BitVec 32)) (nR : Nat) : Nat :=
  (List.range nR).foldl
    (fun acc r => acc + (rp.getD (rm.getD r 0#32).toNat 0#32).toNat) 0

end

public section

theorem bxTermSum_zero (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) :
    bxTermSum nOut σ pool tm tl th bx 0 = 0#nOut := rfl

theorem bxTermSum_succ (nOut : Nat) (σ : Nat → Bool) (pool tm : List (BitVec 32))
    (tl th : List (BitVec 64)) (bx : List (BitVec 32)) (nb : Nat) :
    bxTermSum nOut σ pool tm tl th bx (nb + 1) =
      bxTermSum nOut σ pool tm tl th bx nb +
        termEval nOut σ pool tm tl th (bx.getD nb 0#32).toNat := by
  simp only [bxTermSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bxSymLenSum_zero (pool tm bx : List (BitVec 32)) :
    bxSymLenSum pool tm bx 0 = 0 := rfl

theorem bxSymLenSum_succ (pool tm bx : List (BitVec 32)) (nb : Nat) :
    bxSymLenSum pool tm bx (nb + 1) =
      bxSymLenSum pool tm bx nb +
        (pool.getD (tm.getD (bx.getD nb 0#32).toNat 0#32).toNat 0#32).toNat := by
  simp only [bxSymLenSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rSymLenSum_zero (rp rm : List (BitVec 32)) :
    rSymLenSum rp rm 0 = 0 := rfl

theorem rSymLenSum_succ (rp rm : List (BitVec 32)) (nR : Nat) :
    rSymLenSum rp rm (nR + 1) =
      rSymLenSum rp rm nR + (rp.getD (rm.getD nR 0#32).toNat 0#32).toNat := by
  simp only [rSymLenSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem rSymLenSum_add_nr (rp rm : List (BitVec 32)) (nR : Nat) :
    rSymLenSum rp rm nR + nR = monoTotalWords rp rm nR := by
  induction nR with
  | zero => rfl
  | succ nR ih => rw [rSymLenSum_succ, monoTotalWords_succ]; omega

theorem apply_need_lt_u64 {nb nR slB slR : Nat}
    (hnb : nb < 2 ^ 30) (hslB : slB < 2 ^ 32) (hR : slR + nR ≤ 4000000000) :
    nR * slB + nb * slR < 2 ^ 64 := by
  have h1 : nR * slB ≤ nR * (2 ^ 32 - 1) := Nat.mul_le_mul_left nR (by omega)
  have h2 : nb * slR ≤ (2 ^ 32 - 1) * slR := Nat.mul_le_mul_right slR (by omega)
  have h3 : nR * (2 ^ 32 - 1) + (2 ^ 32 - 1) * slR = (nR + slR) * (2 ^ 32 - 1) := by
    rw [Nat.add_mul, Nat.mul_comm slR]
  have h4 : (nR + slR) * (2 ^ 32 - 1) ≤ 4000000000 * (2 ^ 32 - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h5 : 4000000000 * (2 ^ 32 - 1) < 2 ^ 64 := by decide
  omega

private theorem polyEval_bx_split_aux (nOut : Nat) (σ : Nat → Bool)
    (pool tm : List (BitVec 32)) (tl th : List (BitVec 64)) (bx : List (BitVec 32))
    {nb n : Nat} (hinc : strictIncBelow bx nb n) (hnb : nb ≤ bx.length) :
    ∀ m bp, bp ≤ nb → (∀ p < bp, (bx.getD p 0#32).toNat < m) →
      (bp < nb → m ≤ (bx.getD bp 0#32).toNat) →
      polyEval nOut σ pool tm tl th m =
        nonBxRangeSum nOut σ pool tm tl th bx nb 0 m +
          bxTermSum nOut σ pool tm tl th bx bp := by
  intro m
  induction m with
  | zero =>
    intro bp _ hlo _
    cases bp with
    | zero => simp [polyEval, polyEvalRange_zero, nonBxRangeSum_zero, bxTermSum_zero]
    | succ bp' => exact absurd (hlo bp' (Nat.lt_succ_self _)) (Nat.not_lt_zero _)
  | succ m ih =>
    intro bp hbp_le hlo hhi
    by_cases hhit : ∃ hpos : 0 < bp, (bx.getD (bp - 1) 0#32).toNat = m
    · obtain ⟨hpos, heqm⟩ := hhit
      have hlo' : ∀ p < bp - 1, (bx.getD p 0#32).toNat < m := by
        intro p hp
        have hlt := hinc.2 p (by omega)
        have hmon : ∀ q, p + 1 ≤ q → q ≤ bp - 1 →
            (bx.getD (p + 1) 0#32).toNat ≤ (bx.getD q 0#32).toNat := by
          intro q hpq hqb
          induction q with
          | zero => omega
          | succ q ihq =>
            by_cases hpe : p + 1 = q + 1
            · rw [hpe]; exact le_refl _
            · exact Nat.le_trans (ihq (by omega) (by omega))
                (Nat.le_of_lt (hinc.2 q (by omega)))
        have hle := hmon (bp - 1) (by omega) (le_refl _)
        omega
      have hhi' : bp - 1 < nb → m ≤ (bx.getD (bp - 1) 0#32).toNat := fun _ => by omega
      have hih := ih (bp - 1) (by omega) hlo' hhi'
      have hany := strictIncBelow.any_eq (cur := m) hinc hnb (by omega) hlo' hhi'
      have hb_true : ((bp - 1 < nb) && ((bx.getD (bp - 1) 0#32).toNat == m)) = true := by
        simp only [show bp - 1 < nb by omega, decide_true, Bool.true_and, heqm, beq_self_eq_true]
      rw [hb_true] at hany
      rw [polyEval_succ, hih, nonBxRangeSum_succ, Nat.zero_add, hany, ite_eq_left rfl,
        BitVec.add_zero]
      have hbp_succ : bp = (bp - 1) + 1 := by omega
      conv => rhs; rhs; rw [hbp_succ]
      rw [bxTermSum_succ, heqm, BitVec.add_assoc]
    · have hlo' : ∀ p < bp, (bx.getD p 0#32).toNat < m := by
        intro p hp
        have hlt := hlo p hp
        by_cases hlast : p = bp - 1
        · subst hlast
          have hpos : 0 < bp := by omega
          have hne : (bx.getD (bp - 1) 0#32).toNat ≠ m := fun he => hhit ⟨hpos, he⟩
          omega
        · have h1 := hinc.2 p (by omega)
          have hmon : ∀ q, p + 1 ≤ q → q ≤ bp - 1 →
              (bx.getD (p + 1) 0#32).toNat ≤ (bx.getD q 0#32).toNat := by
            intro q hpq hqb
            induction q with
            | zero => omega
            | succ q ihq =>
              by_cases hpe : p + 1 = q + 1
              · rw [hpe]; exact le_refl _
              · exact Nat.le_trans (ihq (by omega) (by omega))
                  (Nat.le_of_lt (hinc.2 q (by omega)))
          have hle := hmon (bp - 1) (by omega) (le_refl _)
          have hltb := hlo (bp - 1) (by omega)
          omega
      have hhi' : bp < nb → m ≤ (bx.getD bp 0#32).toNat := fun hbp => by
        have := hhi hbp; omega
      have hih := ih bp hbp_le hlo' hhi'
      have hany := strictIncBelow.any_eq (cur := m) hinc hnb hbp_le hlo' hhi'
      have hne_bp : bp < nb → (bx.getD bp 0#32).toNat ≠ m := fun hbp he => by
        have := hhi hbp; omega
      have hb_false : ((bp < nb) && ((bx.getD bp 0#32).toNat == m)) = false := by
        rw [Bool.and_eq_false_iff]
        by_cases hbp : bp < nb
        · right; simp only [beq_eq_false_iff_ne, ne_eq]
          change (bx.getD bp 0#32).toNat ≠ m; exact hne_bp hbp
        · left; simp [hbp]
      rw [hb_false] at hany
      rw [polyEval_succ, hih, nonBxRangeSum_succ, Nat.zero_add, hany,
        ite_eq_right (by decide), BitVec.add_assoc, BitVec.add_comm (bxTermSum _ _ _ _ _ _ _ bp),
        ← BitVec.add_assoc]

theorem polyEval_eq_nonBxTermSum_add_bxTermSum (nOut : Nat) (σ : Nat → Bool)
    (pool tm : List (BitVec 32)) (tl th : List (BitVec 64)) (bx : List (BitVec 32))
    {nb n : Nat} (hinc : strictIncBelow bx nb n) (hnb : nb ≤ bx.length) :
    polyEval nOut σ pool tm tl th n =
      nonBxTermSum nOut σ pool tm tl th bx nb n +
        bxTermSum nOut σ pool tm tl th bx nb :=
  polyEval_bx_split_aux nOut σ pool tm tl th bx hinc hnb n nb (le_refl _)
    (fun p hp => hinc.1 p hp) (fun h => absurd h (Nat.lt_irrefl _))

private theorem bxSymLenSum_le_monoTotalWords_aux (pool tm bx : List (BitVec 32))
    {nb n : Nat} (hinc : strictIncBelow bx nb n) :
    ∀ m bp, bp ≤ nb → (∀ p < bp, (bx.getD p 0#32).toNat < m) →
      (bp < nb → m ≤ (bx.getD bp 0#32).toNat) →
      bxSymLenSum pool tm bx bp + bp ≤ monoTotalWords pool tm m := by
  intro m
  induction m with
  | zero =>
    intro bp _ hlo _
    cases bp with
    | zero => simp [bxSymLenSum_zero, monoTotalWords_zero]
    | succ bp' => exact absurd (hlo bp' (Nat.lt_succ_self _)) (Nat.not_lt_zero _)
  | succ m ih =>
    intro bp hbp_le hlo hhi
    by_cases hhit : ∃ hpos : 0 < bp, (bx.getD (bp - 1) 0#32).toNat = m
    · obtain ⟨hpos, heqm⟩ := hhit
      have hlo' : ∀ p < bp - 1, (bx.getD p 0#32).toNat < m := by
        intro p hp
        have hlt := hinc.2 p (by omega)
        have hmon : ∀ q, p + 1 ≤ q → q ≤ bp - 1 →
            (bx.getD (p + 1) 0#32).toNat ≤ (bx.getD q 0#32).toNat := by
          intro q hpq hqb
          induction q with
          | zero => omega
          | succ q ihq =>
            by_cases hpe : p + 1 = q + 1
            · rw [hpe]; exact le_refl _
            · exact Nat.le_trans (ihq (by omega) (by omega))
                (Nat.le_of_lt (hinc.2 q (by omega)))
        have hle := hmon (bp - 1) (by omega) (le_refl _)
        omega
      have hih := ih (bp - 1) (by omega) hlo' (fun _ => by omega)
      have hbp_succ : bp = (bp - 1) + 1 := by omega
      conv => lhs; rw [hbp_succ]
      rw [bxSymLenSum_succ, heqm, monoTotalWords_succ]
      omega
    · have hlo' : ∀ p < bp, (bx.getD p 0#32).toNat < m := by
        intro p hp
        have hlt := hlo p hp
        by_cases hlast : p = bp - 1
        · subst hlast
          have hpos : 0 < bp := by omega
          have hne : (bx.getD (bp - 1) 0#32).toNat ≠ m := fun he => hhit ⟨hpos, he⟩
          omega
        · have h1 := hinc.2 p (by omega)
          have hmon : ∀ q, p + 1 ≤ q → q ≤ bp - 1 →
              (bx.getD (p + 1) 0#32).toNat ≤ (bx.getD q 0#32).toNat := by
            intro q hpq hqb
            induction q with
            | zero => omega
            | succ q ihq =>
              by_cases hpe : p + 1 = q + 1
              · rw [hpe]; exact le_refl _
              · exact Nat.le_trans (ihq (by omega) (by omega))
                  (Nat.le_of_lt (hinc.2 q (by omega)))
          have hle := hmon (bp - 1) (by omega) (le_refl _)
          have hltb := hlo (bp - 1) (by omega)
          omega
      have hih := ih bp hbp_le hlo' (fun hbp => by have := hhi hbp; omega)
      rw [monoTotalWords_succ]
      omega

theorem bxSymLenSum_add_nb_le_monoTotalWords (pool tm bx : List (BitVec 32))
    {nb n : Nat} (hinc : strictIncBelow bx nb n) :
    bxSymLenSum pool tm bx nb + nb ≤ monoTotalWords pool tm n :=
  bxSymLenSum_le_monoTotalWords_aux pool tm bx hinc n nb (le_refl _)
    (fun p hp => hinc.1 p hp) (fun h => absurd h (Nat.lt_irrefl _))

theorem monoValL_filter_and_sym {σ : Nat → Bool} {mSyms : List Nat} {sym : Nat}
    (hmem : sym ∈ mSyms) :
    (monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) && σ sym) = monoValL σ mSyms := by
  rw [monoValL_eq_decide, monoValL_eq_decide]
  cases hσ : σ sym
  · rw [Bool.and_false]
    exact (decide_eq_false_iff_not.mpr fun hall => absurd (hall sym hmem) (by rw [hσ]; decide)).symm
  · rw [Bool.and_true]
    congr 1
    exact propext
      ⟨fun h s hs => by
        by_cases hse : s = sym
        · subst hse; exact hσ
        · exact h s (List.mem_filter.mpr ⟨hs, decide_eq_true hse⟩),
       fun h s hs => h s (List.mem_filter.mp hs).1⟩

theorem termEval_subst_prod {nOut : Nat} {σ : Nat → Bool} {mSyms mrSyms outSyms : List Nat}
    {sym : Nat} {cl ch rl rh : BitVec 64}
    (hout : ∀ z, z ∈ outSyms ↔ (z ∈ mSyms ∧ z ≠ sym) ∨ z ∈ mrSyms) :
    (if monoValL σ outSyms then coeff128 nOut cl ch * coeff128 nOut rl rh else 0#nOut) =
      (if monoValL σ (mSyms.filter (fun z => decide (z ≠ sym)))
       then coeff128 nOut cl ch else 0#nOut) *
        (if monoValL σ mrSyms then coeff128 nOut rl rh else 0#nOut) := by
  have hm : monoValL σ outSyms =
      (monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) && monoValL σ mrSyms) := by
    rw [monoValL_eq_decide, monoValL_eq_decide, monoValL_eq_decide, Bool.eq_iff_iff,
      Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨fun z hz => h z ((hout z).mpr (Or.inl ?_)),
        fun z hz => h z ((hout z).mpr (Or.inr hz))⟩
      obtain ⟨hz1, hz2⟩ := List.mem_filter.mp hz
      exact ⟨hz1, of_decide_eq_true hz2⟩
    · rintro ⟨h1, h2⟩ z hz
      rcases (hout z).mp hz with ⟨hz1, hz2⟩ | hz3
      · exact h1 z (List.mem_filter.mpr ⟨hz1, decide_eq_true hz2⟩)
      · exact h2 z hz3
  rw [hm]
  cases monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) <;>
    cases monoValL σ mrSyms <;> simp

theorem foldl_mul_left_add {w : Nat} (a : BitVec w) (f : Nat → BitVec w) (n : Nat) :
    (List.range n).foldl (fun acc r => acc + a * f r) 0#w =
      a * (List.range n).foldl (fun acc r => acc + f r) 0#w := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih, BitVec.mul_add]

theorem apply_row_sum_eq {nOut : Nat} {σ : Nat → Bool} {mSyms : List Nat} {sym : Nat}
    {cl ch : BitVec 64} {rp rm : List (BitVec 32)} {rl rh : List (BitVec 64)} {nR : Nat}
    (hmem : sym ∈ mSyms)
    (hCurR : bv nOut (σ sym) = polyEval nOut σ rp rm rl rh nR) :
    (List.range nR).foldl (fun acc r =>
      acc + (if monoValL σ (mSyms.filter (fun z => decide (z ≠ sym)))
             then coeff128 nOut cl ch else 0#nOut) *
        termEval nOut σ rp rm rl rh r) 0#nOut =
      (if monoValL σ mSyms then coeff128 nOut cl ch else 0#nOut) := by
  rw [foldl_mul_left_add]
  have hp : (List.range nR).foldl (fun acc r => acc + termEval nOut σ rp rm rl rh r) 0#nOut =
      polyEval nOut σ rp rm rl rh nR := by
    simp only [polyEval, polyEvalRange, Nat.zero_add]
  rw [hp, ← hCurR, ← monoValL_filter_and_sym (σ := σ) hmem]
  cases hm : monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) <;>
    cases hs : σ sym <;> simp [bv]

theorem monoValL_partner_conflict {σ : Nat → Bool} {nNets : Nat}
    {partnerArr : List (BitVec 32)} {mSyms mrSyms : List Nat} {sym w vqSym : Nat}
    (hPart : PartnerRep σ nNets partnerArr)
    (hw_mem : w ∈ mrSyms) (hw_even : w % 2 = 0) (hw_lt : w / 2 < nNets)
    (hp_ne : partnerArr.getD (w / 2) 0#32 ≠ cNone32)
    (hvq_eq : vqSym = 2 * (partnerArr.getD (w / 2) 0#32).toNat)
    (hvq_ne : vqSym ≠ sym) (hvq_mem : vqSym ∈ mSyms) :
    (monoValL σ (mSyms.filter (fun z => decide (z ≠ sym))) && monoValL σ mrSyms) = false := by
  have hpr := (hPart.2 (w / 2) hw_lt hp_ne).2
  have hw2 : 2 * (w / 2) = w := by omega
  rw [hw2, ← hvq_eq] at hpr
  by_cases hσw : σ w = false
  · rw [monoValL_false_of_mem hw_mem hσw, Bool.and_false]
  · have hσw_t : σ w = true := by cases h : σ w <;> simp_all
    have hσv_f : σ vqSym = false := by cases h : σ vqSym <;> simp_all
    have hfilt : vqSym ∈ mSyms.filter (fun z => decide (z ≠ sym)) :=
      List.mem_filter.mpr ⟨hvq_mem, decide_eq_true hvq_ne⟩
    rw [monoValL_false_of_mem hfilt hσv_f, Bool.false_and]

theorem bxSymLenSum_congr {pool1 pool2 tm1 tm2 bx1 bx2 : List (BitVec 32)} {nb : Nat}
    (hbx : ∀ b < nb, bx1.getD b 0#32 = bx2.getD b 0#32)
    (htm : ∀ b < nb, tm1.getD (bx1.getD b 0#32).toNat 0#32 =
      tm2.getD (bx2.getD b 0#32).toNat 0#32)
    (hp : ∀ b < nb, pool1.getD (tm1.getD (bx1.getD b 0#32).toNat 0#32).toNat 0#32 =
      pool2.getD (tm2.getD (bx2.getD b 0#32).toNat 0#32).toNat 0#32) :
    bxSymLenSum pool1 tm1 bx1 nb = bxSymLenSum pool2 tm2 bx2 nb := by
  induction nb with
  | zero => rfl
  | succ nb ih =>
    rw [bxSymLenSum_succ, bxSymLenSum_succ,
      ih (fun b hb => hbx b (by omega)) (fun b hb => htm b (by omega))
        (fun b hb => hp b (by omega)),
      hp nb (Nat.lt_succ_self nb)]

theorem bxTermSum_congr {nOut : Nat} {σ : Nat → Bool}
    {pool1 pool2 tm1 tm2 bx1 bx2 : List (BitVec 32)} {tl1 th1 tl2 th2 : List (BitVec 64)}
    {nb : Nat}
    (hbx : ∀ b < nb, bx1.getD b 0#32 = bx2.getD b 0#32)
    (hsy : ∀ b < nb, symListAt pool1 (tm1.getD (bx1.getD b 0#32).toNat 0#32).toNat =
      symListAt pool2 (tm2.getD (bx2.getD b 0#32).toNat 0#32).toNat)
    (hc : ∀ b < nb,
      tl1.getD (bx1.getD b 0#32).toNat 0#64 = tl2.getD (bx2.getD b 0#32).toNat 0#64 ∧
      th1.getD (bx1.getD b 0#32).toNat 0#64 = th2.getD (bx2.getD b 0#32).toNat 0#64) :
    bxTermSum nOut σ pool1 tm1 tl1 th1 bx1 nb =
      bxTermSum nOut σ pool2 tm2 tl2 th2 bx2 nb := by
  induction nb with
  | zero => rfl
  | succ nb ih =>
    rw [bxTermSum_succ, bxTermSum_succ,
      ih (fun b hb => hbx b (by omega)) (fun b hb => hsy b (by omega))
        (fun b hb => hc b (by omega))]
    congr 1
    have hc' := hc nb (Nat.lt_succ_self nb)
    simp only [termEval, hsy nb (Nat.lt_succ_self nb), hc'.1, hc'.2]

theorem nonBxRangeSum_congr {nOut : Nat} {σ : Nat → Bool}
    {pool1 pool2 tm1 tm2 bx1 bx2 : List (BitVec 32)} {tl1 th1 tl2 th2 : List (BitVec 64)}
    {nb lo len : Nat} (hnb1 : nb ≤ bx1.length) (hnb2 : nb ≤ bx2.length)
    (hbx : ∀ b < nb, bx1.getD b 0#32 = bx2.getD b 0#32)
    (hsy : ∀ t < len, symListAt pool1 (tm1.getD (lo + t) 0#32).toNat =
      symListAt pool2 (tm2.getD (lo + t) 0#32).toNat)
    (hc : ∀ t < len,
      tl1.getD (lo + t) 0#64 = tl2.getD (lo + t) 0#64 ∧
      th1.getD (lo + t) 0#64 = th2.getD (lo + t) 0#64) :
    nonBxRangeSum nOut σ pool1 tm1 tl1 th1 bx1 nb lo len =
      nonBxRangeSum nOut σ pool2 tm2 tl2 th2 bx2 nb lo len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [nonBxRangeSum_succ, nonBxRangeSum_succ,
      ih (fun t ht => hsy t (by omega)) (fun t ht => hc t (by omega))]
    congr 1
    have hany : (bx1.take nb).any (fun x => x.toNat == lo + len) =
        (bx2.take nb).any (fun x => x.toNat == lo + len) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, List.mem_iff_getElem, List.length_take,
        Nat.min_eq_left hnb1, Nat.min_eq_left hnb2, List.getElem_take]
      constructor
      · rintro ⟨_, ⟨b, hb, rfl⟩, heq⟩
        refine ⟨_, ⟨b, hb, rfl⟩, ?_⟩
        have hb1 := getD_eq_getElem bx1 0#32 (i := b) (by omega)
        have hb2 := getD_eq_getElem bx2 0#32 (i := b) (by omega)
        rw [← hb2, ← hbx b hb, hb1]; exact heq
      · rintro ⟨_, ⟨b, hb, rfl⟩, heq⟩
        refine ⟨_, ⟨b, hb, rfl⟩, ?_⟩
        have hb1 := getD_eq_getElem bx1 0#32 (i := b) (by omega)
        have hb2 := getD_eq_getElem bx2 0#32 (i := b) (by omega)
        rw [← hb1, hbx b hb, hb2]; exact heq
    rw [hany]
    split
    · rfl
    · have hcn := hc len (Nat.lt_succ_self len)
      simp only [termEval, hsy len (Nat.lt_succ_self len), hcn.1, hcn.2]

theorem list_getD_take {α : Type} (xs : List α) (d : α) {n i : Nat} (hi : i < n) :
    (xs.take n).getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ↓reduceIte]

theorem list_getD_append_left {α : Type} (xs ys : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem list_getD_append_right {α : Type} (xs ys : List α) (d : α) {i : Nat}
    (hi : xs.length ≤ i) : (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

theorem symListAt_take_eq {pool : List (BitVec 32)} {off pt : Nat}
    (hsl : MonoSliceOk pool off pt) :
    symListAt (pool.take pt) off = symListAt pool off := by
  have hlen : (pool.take pt).getD off 0#32 = pool.getD off 0#32 := list_getD_take pool 0#32 hsl.1
  simp only [symListAt, hlen]
  apply List.map_congr_left
  intro r hr
  have hrlt := List.mem_range.mp hr
  have h2 := hsl.2
  rw [list_getD_take pool 0#32 (by omega)]

theorem monoSliceOk_take {pool : List (BitVec 32)} {off pt : Nat}
    (hsl : MonoSliceOk pool off pt) (hpt : pt ≤ pool.length) :
    MonoSliceOk (pool.take pt) off (pool.take pt).length := by
  have hlt : (pool.take pt).length = pt := by simp [hpt]
  have hlen : (pool.take pt).getD off 0#32 = pool.getD off 0#32 := list_getD_take pool 0#32 hsl.1
  exact ⟨by rw [hlt]; exact hsl.1, by rw [hlen, hlt]; exact hsl.2⟩

theorem symListAt_congr_take {p1 p2 : List (BitVec 32)} {off pt : Nat}
    (hsl : MonoSliceOk p1 off pt) (hpre : ∀ idx < pt, p2.getD idx 0#32 = p1.getD idx 0#32) :
    symListAt p2 off = symListAt p1 off := by
  have hlen : p2.getD off 0#32 = p1.getD off 0#32 := hpre off hsl.1
  simp only [symListAt, hlen]
  apply List.map_congr_left
  intro r hr
  have hrlt := List.mem_range.mp hr
  have h2 := hsl.2
  rw [hpre (off + 1 + r) (by omega)]

theorem array32_split_at (base : BitVec 64) (xs : List (BitVec 32)) {k : Nat}
    (hk : k ≤ xs.length) :
    array (t := i32) base xs =
      (array (t := i32) base (xs.take k) ⋆
       array (t := i32) (base + BitVec.ofNat 64 (4 * k)) (xs.drop k)) := by
  conv => lhs; rw [← List.take_append_drop k xs]
  rw [array_append, show (i32 : Ty).bytes = 4 from rfl, List.length_take_of_le hk]

theorem array32_join_written (base : BitVec 64) (xs ys zs : List (BitVec 32)) :
    (array (t := i32) base xs ⋆
     array (t := i32) (base + BitVec.ofNat 64 (4 * xs.length)) ys ⋆
     array (t := i32) (base + BitVec.ofNat 64 (4 * (xs.length + ys.length))) zs) =
      array (t := i32) base (xs ++ ys ++ zs) := by
  rw [array_append (t := i32) base (xs ++ ys) zs,
    array_append (t := i32) base xs ys,
    show (i32 : Ty).bytes = 4 from rfl, List.length_append]

theorem poolTail_split (base : BitVec 64) (poolW poolF : List (BitVec 32)) :
    (array (t := i32) base poolW ⋆
     array (t := i32) (base + BitVec.ofNat 64 (4 * poolW.length)) poolF) =
      array (t := i32) base (poolW ++ poolF) := by
  rw [array_append (t := i32) base poolW poolF,
    show (i32 : Ty).bytes = 4 from rfl]

private theorem arrayPad_u8_tail (p : BitVec 64) (xs : List (BitVec 8)) :
    arrayPad i8 p xs =
      (array (t := i8) p xs ⋆
       region (p + BitVec.ofNat 64 xs.length) (align8 xs.length - xs.length)) := by
  simp only [arrayPad, SlabSeg.ofArrayAlign8, SlabSeg.ofArray, Ty.bytes, Ty.size]
  rw [show (8 + 7) / 8 = 1 from rfl, Nat.one_mul]

/-! ## 2. `tMem` / `qMem` Focus Lemma for `ar_apply` -/

theorem tqMem_apply_focus (s : ArCtxState)
    (tm0 tm1 : List (BitVec 32)) (ts0 tl0 th0 ts1 tl1 th1 : List (BitVec 64))
    (pool0 pool1 qm : List (BitVec 32)) (qs ql qh : List (BitVec 64))
    (ix ix2 bx vqOff vq : List (BitVec 32)) (vqSkip : List (BitVec 8))
    (hpc : s.pc.toNat < 2) (htc : s.tc.toNat < 2) :
    let srcPool := if s.pc.toNat = 0 then pool0 else pool1
    let srcTm := if s.tc.toNat = 0 then tm0 else tm1
    let srcTs := if s.tc.toNat = 0 then ts0 else ts1
    let srcTl := if s.tc.toNat = 0 then tl0 else tl1
    let srcTh := if s.tc.toNat = 0 then th0 else th1
    ∃ rest : Mem 64 → Prop,
      (tMem s tm0 tm1 ts0 tl0 th0 ts1 tl1 th1 pool0 pool1 ⋆
        qMem s qm qs ql qh ix ix2 bx vqOff vq vqSkip =
        (array (t := i32) (s.pool.getD s.pc.toNat 0#64) srcPool ⋆
         array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
         array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
         array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
         array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
         array (t := i32) s.qm qm ⋆ array64 s.qs qs ⋆ array64 s.ql ql ⋆ array64 s.qh qh ⋆
         array (t := i32) s.bx bx ⋆ array (t := i32) s.vq_off vqOff ⋆
         array (t := i32) s.vq vq ⋆ array (t := i8) s.vq_skip vqSkip ⋆ rest)) ∧
      (∀ (s' : ArCtxState) (pool' qm' : List (BitVec 32)) (qs' ql' qh' : List (BitVec 64))
          (bx' vqOff' vq' : List (BitVec 32)) (vqSkip' : List (BitVec 8)),
        s'.tm = s.tm → s'.ts = s.ts → s'.tl = s.tl → s'.th = s.th → s'.pool = s.pool →
        s'.qm = s.qm → s'.qs = s.qs → s'.ql = s.ql → s'.qh = s.qh →
        s'.ix = s.ix → s'.ix2 = s.ix2 → s'.bx = s.bx → s'.vq_off = s.vq_off →
        s'.vq = s.vq → s'.vq_skip = s.vq_skip →
        pool'.length = srcPool.length → qm'.length = qm.length →
        qs'.length = qs.length → ql'.length = ql.length → qh'.length = qh.length →
        bx'.length = bx.length → vqOff'.length = vqOff.length →
        vq'.length = vq.length → vqSkip'.length = vqSkip.length →
        tMem s' tm0 tm1 ts0 tl0 th0 ts1 tl1 th1
            (if s.pc.toNat = 0 then pool' else pool0)
            (if s.pc.toNat = 0 then pool1 else pool') ⋆
          qMem s' qm' qs' ql' qh' ix ix2 bx' vqOff' vq' vqSkip' =
          (array (t := i32) (s.pool.getD s.pc.toNat 0#64) pool' ⋆
           array (t := i32) (s.tm.getD s.tc.toNat 0#64) srcTm ⋆
           array64 (s.ts.getD s.tc.toNat 0#64) srcTs ⋆
           array64 (s.tl.getD s.tc.toNat 0#64) srcTl ⋆
           array64 (s.th.getD s.tc.toNat 0#64) srcTh ⋆
           array (t := i32) s.qm qm' ⋆ array64 s.qs qs' ⋆ array64 s.ql ql' ⋆
           array64 s.qh qh' ⋆ array (t := i32) s.bx bx' ⋆ array (t := i32) s.vq_off vqOff' ⋆
           array (t := i32) s.vq vq' ⋆ array (t := i8) s.vq_skip vqSkip' ⋆ rest)) := by
  have hpc' := bv32_lt2_cases hpc
  have htc' := bv32_lt2_cases htc
  have hu32 := arrayPad_u32_unfold
  have hu8 := arrayPad_u8_tail
  rcases hpc' with hp0 | hp1 <;> rcases htc' with ht0 | ht1
  · have hp0' : s.pc.toNat = 0 := by rw [hp0]; rfl
    have ht0' : s.tc.toNat = 0 := by rw [ht0]; rfl
    refine ⟨arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆ array64 (s.ts.getD 1 0#64) ts1 ⋆
      array64 (s.tl.getD 1 0#64) tl1 ⋆ array64 (s.th.getD 1 0#64) th1 ⋆
      arrayPad i32 (s.pool.getD 1 0#64) pool1 ⋆ u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆
      u32PadTail (s.tm.getD 0 0#64) tm0.length ⋆ u32PadTail s.qm qm.length ⋆
      arrayPad i32 s.ix ix ⋆ arrayPad i32 s.ix2 ix2 ⋆ u32PadTail s.bx bx.length ⋆
      u32PadTail s.vq_off vqOff.length ⋆ u32PadTail s.vq vq.length ⋆
      region (s.vq_skip + BitVec.ofNat 64 vqSkip.length)
        (align8 vqSkip.length - vqSkip.length), ?_, ?_⟩
    · simp only [tMem, qMem, hp0', ht0', ↓reduceIte, hu32, hu8]; ac_rfl
    · intro s' pool' qm' qs' ql' qh' bx' vqOff' vq' vqSkip'
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 l1 l2 _ _ _ l6 l7 l8 l9
      simp only [tMem, qMem, hp0', ht0', ↓reduceIte, hu32, hu8, h1, h2, h3, h4, h5, h6, h7, h8, h9,
        h10, h11, h12, h13, h14, h15, l1, l2, l6, l7, l8, l9]; ac_rfl
  · have hp0' : s.pc.toNat = 0 := by rw [hp0]; rfl
    have ht1' : s.tc.toNat = 1 := by rw [ht1]; rfl
    refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      arrayPad i32 (s.pool.getD 1 0#64) pool1 ⋆ u32PadTail (s.pool.getD 0 0#64) pool0.length ⋆
      u32PadTail (s.tm.getD 1 0#64) tm1.length ⋆ u32PadTail s.qm qm.length ⋆
      arrayPad i32 s.ix ix ⋆ arrayPad i32 s.ix2 ix2 ⋆ u32PadTail s.bx bx.length ⋆
      u32PadTail s.vq_off vqOff.length ⋆ u32PadTail s.vq vq.length ⋆
      region (s.vq_skip + BitVec.ofNat 64 vqSkip.length)
        (align8 vqSkip.length - vqSkip.length), ?_, ?_⟩
    · simp only [tMem, qMem, hp0', ht1', show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu32, hu8]
      ac_rfl
    · intro s' pool' qm' qs' ql' qh' bx' vqOff' vq' vqSkip'
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 l1 l2 _ _ _ l6 l7 l8 l9
      simp only [tMem, qMem, hp0', ht1', show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu32, hu8,
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, l1, l2, l6, l7, l8, l9]
      ac_rfl
  · have hp1' : s.pc.toNat = 1 := by rw [hp1]; rfl
    have ht0' : s.tc.toNat = 0 := by rw [ht0]; rfl
    refine ⟨arrayPad i32 (s.tm.getD 1 0#64) tm1 ⋆ array64 (s.ts.getD 1 0#64) ts1 ⋆
      array64 (s.tl.getD 1 0#64) tl1 ⋆ array64 (s.th.getD 1 0#64) th1 ⋆
      arrayPad i32 (s.pool.getD 0 0#64) pool0 ⋆ u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆
      u32PadTail (s.tm.getD 0 0#64) tm0.length ⋆ u32PadTail s.qm qm.length ⋆
      arrayPad i32 s.ix ix ⋆ arrayPad i32 s.ix2 ix2 ⋆ u32PadTail s.bx bx.length ⋆
      u32PadTail s.vq_off vqOff.length ⋆ u32PadTail s.vq vq.length ⋆
      region (s.vq_skip + BitVec.ofNat 64 vqSkip.length)
        (align8 vqSkip.length - vqSkip.length), ?_, ?_⟩
    · simp only [tMem, qMem, hp1', ht0', show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu32, hu8]
      ac_rfl
    · intro s' pool' qm' qs' ql' qh' bx' vqOff' vq' vqSkip'
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 l1 l2 _ _ _ l6 l7 l8 l9
      simp only [tMem, qMem, hp1', ht0', show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu32, hu8,
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, l1, l2, l6, l7, l8, l9]
      ac_rfl
  · have hp1' : s.pc.toNat = 1 := by rw [hp1]; rfl
    have ht1' : s.tc.toNat = 1 := by rw [ht1]; rfl
    refine ⟨arrayPad i32 (s.tm.getD 0 0#64) tm0 ⋆ array64 (s.ts.getD 0 0#64) ts0 ⋆
      array64 (s.tl.getD 0 0#64) tl0 ⋆ array64 (s.th.getD 0 0#64) th0 ⋆
      arrayPad i32 (s.pool.getD 0 0#64) pool0 ⋆ u32PadTail (s.pool.getD 1 0#64) pool1.length ⋆
      u32PadTail (s.tm.getD 1 0#64) tm1.length ⋆ u32PadTail s.qm qm.length ⋆
      arrayPad i32 s.ix ix ⋆ arrayPad i32 s.ix2 ix2 ⋆ u32PadTail s.bx bx.length ⋆
      u32PadTail s.vq_off vqOff.length ⋆ u32PadTail s.vq vq.length ⋆
      region (s.vq_skip + BitVec.ofNat 64 vqSkip.length)
        (align8 vqSkip.length - vqSkip.length), ?_, ?_⟩
    · simp only [tMem, qMem, hp1', ht1', show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu32, hu8]
      ac_rfl
    · intro s' pool' qm' qs' ql' qh' bx' vqOff' vq' vqSkip'
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 l1 l2 _ _ _ l6 l7 l8 l9
      simp only [tMem, qMem, hp1', ht1', show ¬ (1 : Nat) = 0 by decide, ↓reduceIte, hu32, hu8,
        h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, l1, l2, l6, l7, l8, l9]
      ac_rfl

end

end LeanQbe.T.Examples.Arisca.Proof

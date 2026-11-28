/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Limits.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Watch.Spec
public import LeanQbe.T.Examples.Kissat.Src.Congruence

/-!
# Canonical WP Proofs for Congruence XOR Extraction (`#9–#10`)

Proves `Func.wp` against flat `CanonicalEnv` for:
- `9. full_cong_extract_xor_k` (`Spec.fullCongExtractXorKSpec`)
- `10. full_cong_try_xor_ite` (`Spec.fullCongTryXorIteSpec`)
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std Std.Sat
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FidK6Tactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

local macro "cong_split" : tactic =>
  `(tactic| (
    c0_hsteps_nogrp
    repeat (
      refine LeanQbe.T.wp_unroll_group fun _ _ => ?_
      c0_hsteps_nogrp)
    c0_hsplit))

public section

/-! ## Pure XOR Semantic & Structural Helpers -/

private theorem xor1_nat_xor1 (l : Nat) :
    (l ^^^ 1) / 2 = l / 2 ∧ (l ^^^ 1) % 2 = 1 - l % 2 := by
  have h1 : ∀ k, (1 : Nat).testBit (k + 1) = false := fun k => by
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hp : 2 ≤ 2 ^ (k + 1) :=
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hd : 1 / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [hd]
  have hdiv : (l ^^^ 1) / 2 = l / 2 := by
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_xor, h1, Bool.xor_false]
  have hmod : (l ^^^ 1) % 2 = 1 - l % 2 := by
    have h0 : (l ^^^ 1).testBit 0 = !l.testBit 0 := by
      rw [Nat.testBit_xor, show Nat.testBit 1 0 = true from rfl, Bool.xor_true]
    simp only [Nat.testBit_zero] at h0
    rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;>
      rcases Nat.mod_two_eq_zero_or_one (l ^^^ 1) with hn | hn <;> simp_all
  exact ⟨hdiv, hmod⟩

private theorem xor1_evalLitVal_litNeg (α : Nat → Bool) (l : Nat) :
    evalLitVal α (litNeg l) = !evalLitVal α l := by
  unfold evalLitVal litNeg litVar litSign
  obtain ⟨hdiv, hmod⟩ := xor1_nat_xor1 l
  rw [hdiv, hmod]
  cases α (l / 2) <;> rcases Nat.mod_two_eq_zero_or_one l with hm | hm <;> simp [hm]

private theorem xor1_bv32_bit0_eval (α : Nat → Bool) (x : BitVec 32) :
    evalLitVal α x.toNat =
      (evalLitVal α (x &&& ~~~1#32).toNat != decide ((x &&& 1#32) ≠ 0#32)) := by
  rw [m6_bv32_and_not1_toNat]
  unfold evalLitVal litVar litSign
  have hdiv : (2 * (x.toNat / 2)) / 2 = x.toNat / 2 := by omega
  have hmod0 : (2 * (x.toNat / 2)) % 2 = 0 := by omega
  have hb0 : decide ((x &&& 1#32) ≠ 0#32) = decide (x.toNat % 2 = 1) := by
    have h1 : (x &&& 1#32).toNat = x.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    by_cases hm : x.toNat % 2 = 0
    · have hz : (x &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq (by rw [h1, hm]; rfl)
      simp [hz, hm]
    · have ho : x.toNat % 2 = 1 := by omega
      have hnz : (x &&& 1#32) ≠ 0#32 := fun hz => by
        have := congrArg BitVec.toNat hz; rw [h1, ho] at this; cases this
      simp [hnz, ho]
  rw [hdiv, hmod0, hb0]
  cases α (x.toNat / 2) <;> rcases Nat.mod_two_eq_zero_or_one x.toNat with hm | hm <;> simp [hm]

private theorem xor1_bv32_getLsb0_eq_and1 (y : BitVec 32) :
    decide ((y &&& 1#32) ≠ 0#32) = y.getLsbD 0 := by
  have h0 : (y &&& 1#32).toNat = if y.getLsbD 0 then 1 else 0 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod,
      BitVec.getLsbD, Nat.testBit_zero]
    cases hm : y.toNat % 2 == 1 <;> simp_all <;> omega
  cases hg : y.getLsbD 0
  · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h0
    have hz : (y &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq h0
    simp [hz]
  · simp only [hg, ↓reduceIte] at h0
    have hnz : (y &&& 1#32) ≠ 0#32 := fun hz => by
      have := congrArg BitVec.toNat hz; rw [h0] at this; cases this
    simp [hnz]

private theorem xor1_tryIte_xorDefs {f : CNF Nat} {a b cl : Nat}
    (h1 : f.EntailsClause (cnfClause [a, b, cl]))
    (h2 : f.EntailsClause (cnfClause [a, b ^^^ 1, cl ^^^ 1]))
    (h3 : f.EntailsClause (cnfClause [a ^^^ 1, b, cl ^^^ 1]))
    (h4 : f.EntailsClause (cnfClause [a ^^^ 1, b ^^^ 1, cl])) :
    XorGateDef f (litNeg a) b cl ∧ XorGateDef f (litNeg b) a cl ∧
      XorGateDef f (litNeg cl) a b := by
  have hsem : ∀ α : Nat → Bool, f.Sat α →
      (evalLitVal α a != (evalLitVal α b != evalLitVal α cl)) = true := fun α hα => by
    have c1 := (CNF.entails_clause_def.mp h1) α hα
    have c2 := (CNF.entails_clause_def.mp h2) α hα
    have c3 := (CNF.entails_clause_def.mp h3) α hα
    have c4 := (CNF.entails_clause_def.mp h4) α hα
    rw [← clauseEvalVal_iff] at c1 c2 c3 c4
    have hlit_neg : ∀ x, evalLitVal α (x ^^^ 1) = !evalLitVal α x := fun x => by
      simpa [litNeg] using xor1_evalLitVal_litNeg α x
    simp only [clauseEvalVal] at c1 c2 c3 c4
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;>
      cases hc : evalLitVal α cl <;> simp_all
  refine ⟨xorGateDef_of_eval_eq fun α hα => ?_, xorGateDef_of_eval_eq fun α hα => ?_,
    xorGateDef_of_eval_eq fun α hα => ?_⟩ <;>
  · have ht := hsem α hα; rw [xor1_evalLitVal_litNeg]
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;>
      cases hc : evalLitVal α cl <;> simp_all

private def xorKClause (ws : List (BitVec 32)) (k mask : Nat) : List Nat :=
  (List.range k).map fun j => (ws[j]?.getD 0#32).toNat ^^^ ((mask >>> j) &&& 1)

private def xorKBitParity : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => xorKBitParity n m ^^^ ((m >>> n) &&& 1)

private theorem xorKBitParity_eq_foldl :
    ∀ n m : Nat, xorKBitParity n m =
      (List.range n).foldl (fun p j => p ^^^ ((m >>> j) &&& 1)) 0
  | 0, _ => rfl
  | n + 1, m => by
    rw [xorKBitParity, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [xorKBitParity_eq_foldl n m]

private theorem xorKBitParity_lt2 : ∀ n m : Nat, xorKBitParity n m < 2
  | 0, _ => by simp [xorKBitParity]
  | n + 1, m => by
    have ih := xorKBitParity_lt2 n m
    have hb : ((m >>> n) &&& 1) < 2 := by rw [Nat.and_one_is_mod]; omega
    unfold xorKBitParity
    rcases (by omega : xorKBitParity n m = 0 ∨ xorKBitParity n m = 1) with h1 | h1 <;>
      rcases (by omega : (m >>> n) &&& 1 = 0 ∨ (m >>> n) &&& 1 = 1) with h2 | h2 <;>
      simp [h1, h2]

private def xorKMaskRec (α : Nat → Bool) (ws : List (BitVec 32)) : Nat → Nat
  | 0 => 0
  | n + 1 => xorKMaskRec α ws n + if evalLitVal α (ws[n]?.getD 0#32).toNat then 2 ^ n else 0

private theorem xorKMaskRec_lt (α : Nat → Bool) (ws : List (BitVec 32)) :
    ∀ n : Nat, xorKMaskRec α ws n < 2 ^ n
  | 0 => by simp [xorKMaskRec]
  | n + 1 => by
    have ih := xorKMaskRec_lt α ws n
    unfold xorKMaskRec; rw [Nat.pow_succ]; split <;> omega

private theorem xorK_nat_add_two_pow_testBit {x n j : Nat} (hx : x < 2 ^ n) :
    (x + 2 ^ n).testBit j = if j = n then true else x.testBit j := by
  by_cases hjn : j = n
  · subst hjn
    have hd : (x + 2 ^ j) / 2 ^ j = 1 := by
      have h1 : x + 2 ^ j = x + 2 ^ j * 1 := by simp
      rw [h1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt hx]
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
  · simp only [hjn, ↓reduceIte]
    by_cases hlt : j < n
    · simp only [Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ n = 2 ^ j * (2 ^ (n - j - 1) * 2) := by
        rw [← Nat.pow_succ, ← Nat.pow_add]; congr 1; omega
      rw [hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j), Nat.add_mul_mod_self_right]
    · have hgt : n < j := by omega
      have hp : 2 ^ (n + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hgt
      rw [Nat.pow_succ] at hp
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

private theorem xorKMaskRec_bit (α : Nat → Bool) (ws : List (BitVec 32)) :
    ∀ n j : Nat, ((xorKMaskRec α ws n >>> j) &&& 1) =
      if j < n ∧ evalLitVal α (ws[j]?.getD 0#32).toNat = true then 1 else 0
  | 0, j => by simp [xorKMaskRec]
  | n + 1, j => by
    have ih := xorKMaskRec_bit α ws n j
    have hlt := xorKMaskRec_lt α ws n
    have hbit_eq : ∀ x : Nat, ((x >>> j) &&& 1) = if x.testBit j then 1 else 0 := fun x => by
      rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
      rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]
    unfold xorKMaskRec
    rw [hbit_eq (xorKMaskRec α ws n + _)]
    have htb :
        (xorKMaskRec α ws n + if evalLitVal α (ws[n]?.getD 0#32).toNat then 2 ^ n else 0).testBit
            j =
          if j = n then evalLitVal α (ws[n]?.getD 0#32).toNat
          else (xorKMaskRec α ws n).testBit j := by
      cases evalLitVal α (ws[n]?.getD 0#32).toNat
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        by_cases hjn : j = n
        · subst hjn; simp [Nat.testBit_lt_two_pow hlt]
        · simp [hjn]
      · simpa using xorK_nat_add_two_pow_testBit hlt
    rw [htb]
    by_cases hjn : j = n
    · subst hjn
      cases evalLitVal α (ws[j]?.getD 0#32).toNat <;> simp
    · simp only [hjn, ↓reduceIte]
      rw [← hbit_eq (xorKMaskRec α ws n), ih]
      have hlt_iff : (j < n + 1) ↔ (j < n) := by omega
      simp [hlt_iff]

private theorem xorKMaskRec_parity (α : Nat → Bool) (ws : List (BitVec 32)) :
    ∀ n : Nat, xorKBitParity n (xorKMaskRec α ws n) =
      if xorEvalList α ((List.range n).map fun j => (ws[j]?.getD 0#32).toNat) then 1 else 0
  | 0 => by simp [xorKBitParity, xorEvalList]
  | n + 1 => by
    have ih := xorKMaskRec_parity α ws n
    have hbn := xorKMaskRec_bit α ws (n + 1) n
    have hlow : xorKBitParity n (xorKMaskRec α ws (n + 1)) =
        xorKBitParity n (xorKMaskRec α ws n) := by
      have hrec : ∀ q ≤ n,
          xorKBitParity q (xorKMaskRec α ws (n + 1)) =
            xorKBitParity q (xorKMaskRec α ws n) := fun q => by
        induction q with
        | zero => intro _; rfl
        | succ q ihq =>
          intro hqn
          unfold xorKBitParity
          rw [ihq (by omega), xorKMaskRec_bit α ws (n + 1) q, xorKMaskRec_bit α ws n q]
          have h1 : q < n + 1 ↔ q < n := by omega
          simp [h1]
      exact hrec n (Nat.le_refl _)
    rw [xorKBitParity, hlow, ih, List.range_succ, List.map_append, List.map_singleton,
      xorEvalList_append, xorEvalList_cons, xorEvalList_nil, Bool.bne_false]
    simp only [Nat.lt_succ_self, true_and] at hbn
    rw [hbn]
    cases xorEvalList α ((List.range n).map fun j => (ws[j]?.getD 0#32).toNat) <;>
      cases evalLitVal α (ws[n]?.getD 0#32).toNat <;> simp

private theorem xorK_clauseEvalVal_mem (α : Nat → Bool) :
    ∀ {l : List Nat}, clauseEvalVal α l = true → ∃ x ∈ l, evalLitVal α x = true
  | [], h => by simp [clauseEvalVal] at h
  | x :: xs, h => by
    simp only [clauseEvalVal] at h
    rcases (Bool.or_eq_true _ _).mp h with hx | hxs
    · exact ⟨x, List.mem_cons_self, hx⟩
    · obtain ⟨y, hy, hyt⟩ := xorK_clauseEvalVal_mem α hxs
      exact ⟨y, List.mem_cons_of_mem x hy, hyt⟩

private theorem xorK_eval_odd_of_even_clauses {ws : List (BitVec 32)} {k : Nat}
    {F_cur : List (List Nat)}
    (heven : ∀ m < 2 ^ k, xorKBitParity k m = 0 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause (xorKClause ws k m))) :
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      xorEvalList α ((List.range k).map fun j => (ws[j]?.getD 0#32).toNat) = true := by
  intro α hα
  cases hxf : xorEvalList α ((List.range k).map fun j => (ws[j]?.getD 0#32).toNat)
  case true => rfl
  case false =>
    let m := xorKMaskRec α ws k
    have hm_lt : m < 2 ^ k := xorKMaskRec_lt α ws k
    have hpar0 : xorKBitParity k m = 0 := by
      dsimp only [m]; rw [xorKMaskRec_parity, hxf]; rfl
    have hcl := (CNF.entails_clause_def.mp (heven m hm_lt hpar0)) α hα
    rw [← clauseEvalVal_iff] at hcl
    obtain ⟨l, hl_mem, hl_true⟩ := xorK_clauseEvalVal_mem α hcl
    unfold xorKClause at hl_mem
    rw [List.mem_map] at hl_mem
    obtain ⟨j, hj_mem, rfl⟩ := hl_mem
    rw [List.mem_range] at hj_mem
    rw [xorKMaskRec_bit α ws k j] at hl_true
    simp only [hj_mem, true_and] at hl_true
    cases hb : evalLitVal α (ws[j]?.getD 0#32).toNat
    · simp [hb] at hl_true
    · simp only [hb, ↓reduceIte] at hl_true
      change evalLitVal α (litNeg (ws[j]?.getD 0#32).toNat) = true at hl_true
      rw [xor1_evalLitVal_litNeg, hb] at hl_true; cases hl_true

private theorem xorK_gate4_defs {F_cur : List (List Nat)} {l0 l1 l2 l3 : Nat}
    (hodd : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      xorEvalList α [l0, l1, l2, l3] = true) :
    XorListGateDef (cnfOfClauses F_cur) (litNeg l0) [l1, l2, l3] ∧
    XorListGateDef (cnfOfClauses F_cur) (litNeg l1) [l0, l2, l3] ∧
    XorListGateDef (cnfOfClauses F_cur) (litNeg l2) [l0, l1, l3] ∧
    XorListGateDef (cnfOfClauses F_cur) (litNeg l3) [l0, l1, l2] := by
  have hbase : ∀ a b c d : Nat, List.Perm [a, b, c, d] [l0, l1, l2, l3] →
      XorListGateDef (cnfOfClauses F_cur) (litNeg a) [b, c, d] := fun a b c d hp α hα => by
    have hx := hodd α hα
    rw [← xorEvalList_perm α hp, xorEvalList_cons] at hx
    rw [xor1_evalLitVal_litNeg]
    cases ha : evalLitVal α a <;> cases hbcd : xorEvalList α [b, c, d] <;> simp_all
  exact ⟨hbase _ _ _ _ (List.Perm.refl _),
    hbase _ _ _ _ (List.Perm.swap l0 l1 [l2, l3]),
    hbase _ _ _ _ ((List.Perm.swap l0 l2 [l1, l3]).trans
      (List.Perm.cons l0 (List.Perm.swap l1 l2 [l3]))),
    hbase _ _ _ _ ((List.Perm.swap l0 l3 [l1, l2]).trans
      ((List.Perm.cons l0 (List.Perm.swap l1 l3 [l2])).trans
        (List.Perm.cons l0 (List.Perm.cons l1 (List.Perm.swap l2 l3 [])))))⟩

private theorem xorK_foldl_parity_step (zs : List (BitVec 32)) :
    ∀ init : Nat, init < 2 →
      zs.foldl (fun acc y => acc ^^^ (y.toNat % 2)) init < 2 ∧
      zs.foldl (fun acc y => acc ^^^ (y.toNat % 2)) init =
        (init ^^^ zs.foldl (fun acc y => acc ^^^ (y.toNat % 2)) 0) := by
  induction zs with
  | nil => intro init h2; simp [h2]
  | cons z zs ih =>
    intro init h2
    have hz : z.toNat % 2 = 0 ∨ z.toNat % 2 = 1 := Nat.mod_two_eq_zero_or_one _
    have hi : init = 0 ∨ init = 1 := by omega
    have hlt1 : init ^^^ (z.toNat % 2) < 2 := by
      rcases hi with rfl | rfl <;> rcases hz with h | h <;> simp [h]
    have ⟨h1, he1⟩ := ih (init ^^^ (z.toNat % 2)) hlt1
    have ⟨_, he2⟩ := ih (z.toNat % 2) (by omega)
    refine ⟨h1, ?_⟩
    simp only [List.foldl_cons, Nat.zero_xor]
    rw [he1, he2, Nat.xor_assoc]

private theorem xorK_gateK_def {F_cur : List (List Nat)} {ws : List (BitVec 32)} {k i : Nat}
    {neg_p : BitVec 32} {rhs_s : List (BitVec 32)}
    (hik : i < k)
    (hodd : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      xorEvalList α ((List.range k).map fun j => (ws[j]?.getD 0#32).toNat) = true)
    (hnp : (neg_p &&& 1#32).toNat = (List.range k).foldl
      (fun acc j => acc ^^^ ((ws[j]?.getD 0#32).toNat % 2)) 0)
    (hperm : List.Perm rhs_s
      (((List.range k).filter (· ≠ i)).map fun j => ws[j]?.getD 0#32 &&& ~~~1#32)) :
    let lhs := (ws[i]?.getD 0#32 &&& ~~~1#32) ||| (1#32 ^^^ (neg_p &&& 1#32))
    XorListGateDef (cnfOfClauses F_cur) lhs.toNat (rhs_s.map BitVec.toNat) := by
  intro lhs α hα
  have hodd_α := hodd α hα
  rw [xorEvalList_perm α (hperm.map BitVec.toNat)]
  have hsplit : ∀ n, i < n →
      List.Perm ((List.range n).map fun j => ws[j]?.getD 0#32)
        (ws[i]?.getD 0#32 :: ((List.range n).filter (· ≠ i)).map fun j =>
          ws[j]?.getD 0#32) := by
    intro n hin; induction n with
    | zero => omega
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, List.filter_append,
        List.filter_cons, List.filter_nil]
      by_cases hni : n = i
      · subst hni
        simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
          List.append_nil]
        have hfilt : (List.range n).filter (· ≠ n) = List.range n := by
          rw [List.filter_eq_self]
          intro q hq; rw [List.mem_range] at hq; simp [Nat.ne_of_lt hq]
        rw [hfilt]
        exact List.perm_append_singleton (ws[n]?.getD 0#32) _
      · simp only [ne_eq, hni, not_false_eq_true, decide_true, ↓reduceIte, List.map_append,
          List.map_singleton]
        exact (ih (by omega)).append_right _
  have hperm_all := hsplit k hik
  have hfold_parity : ∀ l : List (BitVec 32),
      xorEvalList α (l.map BitVec.toNat) =
        (xorEvalList α (l.map fun x => (x &&& ~~~1#32).toNat) !=
          decide (l.foldl (fun acc x => acc ^^^ (x.toNat % 2)) 0 = 1)) := fun l => by
    induction l with
    | nil => simp [xorEvalList]
    | cons x xs ih =>
      simp only [List.map_cons, xorEvalList_cons, ih, List.foldl_cons, Nat.zero_xor]
      rw [xor1_bv32_bit0_eval α x]
      have ⟨hf2, _⟩ := xorK_foldl_parity_step xs 0 (by decide)
      have ⟨_, heq⟩ := xorK_foldl_parity_step xs (x.toNat % 2) (Nat.mod_lt _ (by decide))
      rw [heq]
      have hhb : decide ((x &&& 1#32) ≠ 0#32) = decide (x.toNat % 2 = 1) := by
        have h1 : (x &&& 1#32).toNat = x.toNat % 2 := by
          rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
        rcases Nat.mod_two_eq_zero_or_one x.toNat with hm | hm
        · have hz : x &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq (by rw [h1, hm]; rfl)
          simp [hz, hm]
        · have hnz : x &&& 1#32 ≠ 0#32 := fun hz => by
            have := congrArg BitVec.toNat hz; rw [h1, hm] at this; cases this
          simp [hnz, hm]
      rw [hhb]
      rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
        rcases (by omega : xs.foldl (fun acc y => acc ^^^ (y.toNat % 2)) 0 = 0 ∨
          xs.foldl (fun acc y => acc ^^^ (y.toNat % 2)) 0 = 1) with hxs | hxs <;>
        cases evalLitVal α (x &&& ~~~1#32).toNat <;>
        cases xorEvalList α (xs.map fun y => (y &&& ~~~1#32).toNat) <;>
        simp [hx, hxs]
  let raw_list := (List.range k).map fun j => ws[j]?.getD 0#32
  have hev_all : xorEvalList α (raw_list.map BitVec.toNat) = true := by
    simpa [raw_list, Function.comp_def] using hodd_α
  rw [hfold_parity raw_list] at hev_all
  have hfold_eq : raw_list.foldl (fun acc x => acc ^^^ (x.toNat % 2)) 0 =
      (neg_p &&& 1#32).toNat := by
    rw [hnp]; dsimp only [raw_list]; clear hev_all
    have hgen : ∀ n init, (List.map (fun j => ws[j]?.getD 0#32) (List.range n)).foldl
        (fun acc x => acc ^^^ (x.toNat % 2)) init = (List.range n).foldl
          (fun acc j => acc ^^^ ((ws[j]?.getD 0#32).toNat % 2)) init := fun n => by
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro init
        rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
          List.foldl_append, ih, List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    exact hgen k 0
  have hlhs_eval : evalLitVal α lhs.toNat =
      (evalLitVal α (ws[i]?.getD 0#32 &&& ~~~1#32).toNat !=
        !(decide ((neg_p &&& 1#32).toNat = 1))) := by
    have hnp_lt : (neg_p &&& 1#32).toNat = 0 ∨ (neg_p &&& 1#32).toNat = 1 := by
      rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
      exact Nat.mod_two_eq_zero_or_one _
    rcases hnp_lt with h | h
    · have hb0 : neg_p &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq h
      have hln : lhs.toNat = litNeg (ws[i]?.getD 0#32 &&& ~~~1#32).toNat := by
        have hx : (1#32 : BitVec 32) ^^^ 0#32 = 1#32 &&& 1#32 := by decide
        have hl1 : lhs.toNat = 2 * ((ws[i]?.getD 0#32).toNat / 2) + 1 := by
          dsimp only [lhs]; rw [hb0, hx, bv32_even_or_bit_toNat]; rfl
        have ⟨_, hm1⟩ := xor1_nat_xor1 (ws[i]?.getD 0#32 &&& ~~~1#32).toNat
        have hd1 := (xor1_nat_xor1 (ws[i]?.getD 0#32 &&& ~~~1#32).toNat).1
        have hev := m6_bv32_and_not1_toNat (ws[i]?.getD 0#32)
        unfold litNeg; rw [hl1]; omega
      rw [hln, xor1_evalLitVal_litNeg, h, show decide (0 = 1) = false from rfl, Bool.not_false,
        Bool.bne_true]
    · have hb1 : neg_p &&& 1#32 = 1#32 := BitVec.eq_of_toNat_eq h
      have hln : lhs = ws[i]?.getD 0#32 &&& ~~~1#32 := by
        dsimp only [lhs]
        rw [hb1, show (1#32 : BitVec 32) ^^^ 1#32 = 0#32 from by decide, BitVec.or_zero]
      rw [hln, h, show decide (1 = 1) = true from rfl, Bool.not_true, Bool.bne_false]
  have hperm_pos : List.Perm (raw_list.map fun x => (x &&& ~~~1#32).toNat)
      ((ws[i]?.getD 0#32 &&& ~~~1#32).toNat ::
        (((List.range k).filter (· ≠ i)).map fun j =>
          (ws[j]?.getD 0#32 &&& ~~~1#32).toNat)) := by
    have hp := hperm_all.map fun x => (x &&& ~~~1#32).toNat
    dsimp only [raw_list] at hp ⊢
    simp only [List.map_cons, List.map_map, Function.comp_def] at hp ⊢
    exact hp
  have hx_pos := xorEvalList_perm α hperm_pos
  rw [xorEvalList_cons] at hx_pos
  rw [hfold_eq] at hev_all
  change (xorEvalList α (raw_list.map fun x => (x &&& ~~~1#32).toNat) != _) = true at hev_all
  rw [hx_pos] at hev_all
  rw [hlhs_eval]
  simp only [List.map_map, Function.comp_def]
  cases h1 : evalLitVal α (ws[i]?.getD 0#32 &&& ~~~1#32).toNat <;>
    cases h2 : xorEvalList α (((List.range k).filter (· ≠ i)).map fun j =>
      (ws[j]?.getD 0#32 &&& ~~~1#32).toNat) <;>
    cases h3 : decide ((neg_p &&& 1#32).toNat = 1) <;> simp_all

private theorem xorK_emit_gateAt {maxA cur_vars : Nat} {F_cur : List (List Nat)}
    {scr : List (BitVec 32)} {g_len k : Nat} {lhs mword : BitVec 32}
    (hmax4 : 4 ≤ maxA) (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (hkcv : k ≤ cur_vars)
    (hbd : g_len + 2 + (k - 1) ≤ scr.length)
    (h0 : scr[g_len]? = some lhs) (h1 : scr[g_len + 1]? = some mword)
    (hmword : mword = (1#32 <<< 28) ||| BitVec.ofNat 32 (k - 1))
    (hlhs : lhs.toNat < 2 * cur_vars)
    (hrhs : ∀ q < k - 1, ∃ r : BitVec 32, scr[g_len + 2 + q]? = some r ∧ r.toNat < 2 * cur_vars)
    (hdef : XorListGateDef (cnfOfClauses F_cur) lhs.toNat
      (((scr.drop (g_len + 2)).take (k - 1)).map BitVec.toNat)) :
    CongGateAt maxA F_cur cur_vars scr (g_len + 2 + (k - 1)) g_len := by
  have har : congGateArity mword = k - 1 := by
    rw [hmword]; rcases (by omega : k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl <;> decide
  have htag : (mword >>> 28).toNat = 1 := by
    rw [hmword]; rcases (by omega : k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl <;> decide
  refine ⟨lhs, mword, h0, h1, hlhs, ?_, ?_, ?_, ?_, Or.inr (Or.inl ⟨htag, ?_, ?_, ?_⟩)⟩
  · rw [har]; omega
  · rw [har]; omega
  · rw [har]; omega
  · rw [har]; exact hrhs
  · rw [har]; omega
  · rw [har]; omega
  · rw [har]; exact hdef

private theorem xorK_tmp_lit_bd {w b : BitVec 32} {cur_vars : Nat}
    (hw : w.toNat < 2 * cur_vars) (hb : b = 0#32 ∨ b = 1#32) :
    (w ^^^ b).toNat < 2 * cur_vars ∧ (w ^^^ b).toNat / 2 = w.toNat / 2 := by
  rcases hb with rfl | rfl
  · simp [hw]
  · rw [bv32_xor1_eq_litNeg]
    exact ⟨litNeg_lt_two_mul hw, (xor1_nat_xor1 w.toNat).1⟩

private theorem xorK_take_eq_range_map {α : Type _} [Inhabited α] (xs : List α) (n : Nat)
    (hn : n ≤ xs.length) : xs.take n = (List.range n).map fun q => xs[q]?.getD default := by
  apply List.ext_getElem
  · simp [List.length_take, hn]
  · intro i hi _
    simp only [List.length_take, Nat.min_eq_left hn] at hi
    rw [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]

private theorem xorK_perm_set_step {xs ws : List (BitVec 32)} {cnt j i : Nat}
    (hlen : cnt < xs.length) (hj : j < ws.length)
    (hperm : List.Perm ((List.range cnt).map fun q => xs[q]?.getD 0#32)
      (((List.range j).filter (· ≠ i)).map fun q => ws[q]?.getD 0#32 &&& ~~~1#32))
    (hne : j ≠ i) :
    List.Perm ((List.range (cnt + 1)).map fun q =>
        (xs.set cnt (ws[j] &&& ~~~1#32))[q]?.getD 0#32)
      (((List.range (j + 1)).filter (· ≠ i)).map fun q => ws[q]?.getD 0#32 &&& ~~~1#32) := by
  have hL : ((List.range (cnt + 1)).map fun q =>
      (xs.set cnt (ws[j] &&& ~~~1#32))[q]?.getD 0#32) =
      ((List.range cnt).map fun q => xs[q]?.getD 0#32) ++ [ws[j] &&& ~~~1#32] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
    congr 1
    · refine List.map_congr_left fun q hq => ?_
      rw [List.mem_range] at hq
      rw [List.getElem?_set_ne (by omega)]
    · rw [List.getElem?_set_self hlen, Option.getD_some]
  have hR : (((List.range (j + 1)).filter (· ≠ i)).map fun q => ws[q]?.getD 0#32 &&& ~~~1#32) =
      (((List.range j).filter (· ≠ i)).map fun q => ws[q]?.getD 0#32 &&& ~~~1#32) ++
        [ws[j] &&& ~~~1#32] := by
    rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
    have hd : decide (j ≠ i) = true := by simp [hne]
    rw [hd]; simp only [↓reduceIte, List.map_append, List.map_singleton]
    rw [List.getElem?_eq_getElem hj, Option.getD_some]
  rw [hL, hR]; exact hperm.append_right _

private theorem xorK_scr_drop_take_eq (scr tmps : List (BitVec 32)) (g k1 : Nat)
    (hlen : g + k1 ≤ scr.length) (htmpl : k1 ≤ tmps.length)
    (hcov : ∀ r < k1, scr[g + r]? = tmps[r]?) :
    (scr.drop g).take k1 = tmps.take k1 := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro q hq _
    simp only [List.length_take, List.length_drop,
      Nat.min_eq_left (by omega : k1 ≤ scr.length - g)] at hq
    rw [List.getElem_take, List.getElem_drop, List.getElem_take, ← Option.some_inj,
      ← List.getElem?_eq_getElem (by omega), ← List.getElem?_eq_getElem (by omega)]
    exact hcov q hq

private theorem xorK_cap_ok {k : BitVec 32} {g_len g_cap : BitVec 64} {scratch_cap : Nat}
    (hk3 : 3 ≤ k.toNat) (hk5 : k.toNat ≤ 5)
    (hg_le : g_len.toNat ≤ g_cap.toNat) (hg_cap : g_cap.toNat ≤ scratch_cap)
    (hsc : scratch_cap < 2 ^ 28)
    (hc : ¬g_cap.toNat < (g_len.toNat + k.toNat * ((k.toNat + 1) % 2 ^ 32)) % 2 ^ 64) :
    g_len.toNat + k.toNat * (k.toNat + 1) ≤ g_cap.toNat := by
  have hk1 : (k.toNat + 1) % 2 ^ 32 = k.toNat + 1 := Nat.mod_eq_of_lt (by omega)
  have hk_prod : k.toNat * (k.toNat + 1) ≤ 30 := by
    rcases (by omega : k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 5) with h | h | h <;> simp [h]
  rw [hk1, Nat.mod_eq_of_lt (by omega)] at hc; omega

private theorem xorK_wvec_bounds {w3 : BitVec 32} {cur_vars max_vars wvec_len ws1_len : Nat}
    (hw3 : w3.toNat < 2 * cur_vars) (hcv : cur_vars ≤ max_vars)
    (hwvl : wvec_len = 4 * max_vars) (hws1l : ws1_len = 2 * max_vars) :
    (((w3 &&& ~~~1#32).setWidth 64 <<< 1#64) + 1#64).toNat < wvec_len ∧
    ((((w3 &&& ~~~1#32) ||| 1#32).setWidth 64 <<< 1#64) + 1#64).toNat < wvec_len ∧
    (((w3 &&& ~~~1#32) ^^^ 1#32).setWidth 64).toNat < ws1_len ∧
    ((((w3 &&& ~~~1#32) ||| 1#32) ^^^ 1#32).setWidth 64).toNat < ws1_len ∧
    ((((w3 &&& ~~~1#32) ^^^ 1#32).setWidth 64 <<< 1#64) + 1#64).toNat < wvec_len ∧
    (((((w3 &&& ~~~1#32) ||| 1#32) ^^^ 1#32).setWidth 64 <<< 1#64) + 1#64).toNat < wvec_len := by
  have hev := m6_bv32_and_not1_toNat w3
  have hpos : (w3 &&& ~~~1#32).toNat < 2 * cur_vars := by rw [hev]; omega
  have hor : ((w3 &&& ~~~1#32) ||| 1#32).toNat < 2 * cur_vars := by
    rw [show (w3 &&& ~~~1#32 ||| 1#32) = (w3 &&& ~~~1#32 ||| 1#32 &&& 1#32) from rfl,
      bv32_even_or_bit_toNat]; omega
  have hx1 : ((w3 &&& ~~~1#32) ^^^ 1#32).toNat < 2 * cur_vars := by
    rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul hpos
  have ho1 : (((w3 &&& ~~~1#32) ||| 1#32) ^^^ 1#32).toNat < 2 * cur_vars := by
    rw [bv32_xor1_eq_litNeg]; exact litNeg_lt_two_mul hor
  have hw1 : ∀ x : BitVec 32, x.toNat < 2 * cur_vars → (x.setWidth 64).toNat < ws1_len :=
    fun x hx => by rw [bv_zext32_toNat]; omega
  have hstep : ∀ x : BitVec 32, x.toNat < 2 * cur_vars →
      ((x.setWidth 64 <<< 1#64) + 1#64).toNat < wvec_len := fun x hx => by
    have hsh : (x.setWidth 64 <<< 1#64).toNat = 2 * x.toNat := by
      change (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat
      rw [BitVec.toNat_shiftLeft, bv_zext32_toNat, Nat.shiftLeft_eq, Nat.mul_comm,
        Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hsh, show (1#64 : BitVec 64).toNat = 1 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    omega
  exact ⟨hstep _ hpos, hstep _ hor, hw1 _ hx1, hw1 _ ho1, hstep _ hx1, hstep _ ho1⟩

private theorem xorK_tmp_bounds {tmp ws2 : List (BitVec 32)} {k cur_vars : Nat}
    {mask : BitVec 32} (hcov : ∀ r < k, (tmp[r]?.getD 0#32).toNat =
      (ws2[r]?.getD 0#32).toNat ^^^ ((mask.toNat >>> r) &&& 1))
    (hws2 : ∀ j < k, (ws2[j]?.getD 0#32).toNat < 2 * cur_vars)
    (hnodup : ∀ a b, a < b → b < k →
      (ws2[a]?.getD 0#32).toNat / 2 ≠ (ws2[b]?.getD 0#32).toNat / 2) :
    (∀ j < k, (tmp[j]?.getD 0#32).toNat < 2 * cur_vars) ∧
      (∀ a b, a < b → b < k →
        (tmp[a]?.getD 0#32).toNat / 2 ≠ (tmp[b]?.getD 0#32).toNat / 2) := by
  have hbit : ∀ r, ((mask.toNat >>> r) &&& 1) = 0 ∨ ((mask.toNat >>> r) &&& 1) = 1 := fun r => by
    rw [Nat.and_one_is_mod]; exact Nat.mod_two_eq_zero_or_one _
  have hdiv : ∀ x m : Nat, (m = 0 ∨ m = 1) → (x ^^^ m) / 2 = x / 2 := fun x m hm => by
    rcases hm with rfl | rfl
    · simp
    · exact (xor1_nat_xor1 x).1
  refine ⟨fun j hj => ?_, fun a b hab hbk => ?_⟩
  · rw [hcov j hj]
    rcases hbit j with h | h
    · simp [h, hws2 j hj]
    · rw [h]; exact litNeg_lt_two_mul (hws2 j hj)
  · rw [hcov a (by omega), hcov b hbk, hdiv _ _ (hbit a), hdiv _ _ (hbit b)]
    exact hnodup a b hab hbk

private theorem xorK_emit_gate_post {maxA cur_vars : Nat} {F_cur : List (List Nat)}
    {ws2 scr0 scr5 scr_q tmp_s : List (BitVec 32)} {g_len k i scratch_cap tmp_len : Nat}
    {cur_g : BitVec 64} {kv neg_p lhs mword : BitVec 32}
    (hmax4 : 4 ≤ maxA) (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (hkcv : k ≤ cur_vars) (hkv : kv.toNat = k)
    (hi_lt : i < k) (hcg_eq : cur_g.toNat = g_len + i * (k + 1))
    (hcap_le : g_len + (i + 1) * (k + 1) ≤ scratch_cap) (hsc : scratch_cap < 2 ^ 28)
    (hscr5l : scr5.length = scratch_cap) (hscrl_q : scr_q.length = scratch_cap)
    (htmpl_s : tmp_s.length = tmp_len) (hk1_le : k - 1 ≤ tmp_len)
    (hws2_lt : ∀ j < k, (ws2[j]?.getD 0#32).toNat < 2 * cur_vars)
    (hodd : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      xorEvalList α ((List.range k).map fun j => (ws2[j]?.getD 0#32).toNat) = true)
    (hnp_par : (neg_p &&& 1#32).toNat = (List.range k).foldl
      (fun acc j => acc ^^^ ((ws2[j]?.getD 0#32).toNat % 2)) 0)
    (hlhs : lhs = (ws2[i]?.getD 0#32 &&& ~~~1#32) ||| (1#32 ^^^ (neg_p &&& 1#32)))
    (hmword : mword = (1#32 <<< 28) ||| (kv - 1#32))
    (hpres5 : ∀ idx < g_len, scr5[idx]? = scr0[idx]?)
    (hseq5 : CongGateSeqOk maxA F_cur cur_vars scr5 cur_g.toNat 0)
    (hpres_q : ∀ idx < cur_g.toNat + 2,
      scr_q[idx]? = ((scr5.set cur_g.toNat lhs).set (cur_g + 1#64).toNat mword)[idx]?)
    (hcov_q : ∀ r < k - 1, scr_q[cur_g.toNat + 2 + r]? = tmp_s[r]?)
    (hperm_all : List.Perm (tmp_s.take (k - 1))
      (((List.range k).filter (· ≠ i)).map fun q => ws2[q]?.getD 0#32 &&& ~~~1#32)) :
    (∀ idx < g_len, scr_q[idx]? = scr0[idx]?) ∧
      CongGateSeqOk maxA F_cur cur_vars scr_q (g_len + (i + 1) * (k + 1)) 0 := by
  have hcap_exp : g_len + i * (k + 1) + (k + 1) ≤ scratch_cap := by
    rw [Nat.add_mul, Nat.one_mul] at hcap_le; omega
  have hcg1_eq : (cur_g + 1#64).toNat = cur_g.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt]
    rw [hcg_eq]; omega
  have hdrop_s : (scr_q.drop (cur_g.toNat + 2)).take (k - 1) = tmp_s.take (k - 1) :=
    xorK_scr_drop_take_eq scr_q tmp_s (cur_g.toNat + 2) (k - 1)
      (by omega) (by omega) hcov_q
  have h0_scr : scr_q[cur_g.toNat]? = some lhs := by
    rw [hpres_q _ (by omega), List.getElem?_set_ne (by rw [hcg1_eq]; omega),
      List.getElem?_set_self (by omega)]
  have h1_scr : scr_q[cur_g.toNat + 1]? = some mword := by
    rw [hpres_q _ (by omega), ← hcg1_eq]
    exact List.getElem?_set_self (by rw [List.length_set, hscr5l, hcg1_eq]; omega)
  have hk_eq : kv = BitVec.ofNat 32 k := BitVec.eq_of_toNat_eq (by simp [hkv]; omega)
  have hmword_eq : mword = (1#32 <<< 28) ||| BitVec.ofNat 32 (k - 1) := by
    rw [hmword, hk_eq]
    rcases (by omega : k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl <;> decide
  have hgate_at : CongGateAt maxA F_cur cur_vars scr_q (g_len + (i + 1) * (k + 1))
      cur_g.toNat := by
    have hext : cur_g.toNat + 2 + (k - 1) = g_len + (i + 1) * (k + 1) := by
      rw [hcg_eq, Nat.add_mul]; omega
    rw [← hext]
    refine xorK_emit_gateAt hmax4 hk3 hk5 hkcv (by omega) h0_scr h1_scr hmword_eq ?_ ?_ ?_
    · have hl_ws := hws2_lt i hi_lt
      have hm2 : (neg_p &&& 1#32).toNat = 0 ∨ (neg_p &&& 1#32).toNat = 1 := by
        rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
        exact Nat.mod_two_eq_zero_or_one _
      rcases hm2 with hnp_v | hnp_v
      · have h0' : neg_p &&& 1#32 = 0#32 := BitVec.eq_of_toNat_eq hnp_v
        rw [hlhs, h0', show (1#32 : BitVec 32) ^^^ 0#32 = 1#32 &&& 1#32 from by decide,
          bv32_even_or_bit_toNat]; omega
      · have h1' : neg_p &&& 1#32 = 1#32 := BitVec.eq_of_toNat_eq hnp_v
        rw [hlhs, h1', show (1#32 : BitVec 32) ^^^ 1#32 = 0#32 from by decide, BitVec.or_zero,
          m6_bv32_and_not1_toNat]; omega
    · intro r hr
      have hr_lt : r < (tmp_s.take (k - 1)).length := by simp [List.length_take, htmpl_s]; omega
      have hrm : tmp_s[r]'(by rw [htmpl_s]; omega) ∈ tmp_s.take (k - 1) := by
        rw [← List.getElem_take (i := r) (h := hr_lt)]; exact List.getElem_mem _
      have hm2 := hperm_all.mem_iff.mp hrm
      rw [List.mem_map] at hm2
      obtain ⟨u, hu, hu_eq⟩ := hm2
      rw [List.mem_filter, List.mem_range] at hu
      refine ⟨ws2[u]?.getD 0#32 &&& ~~~1#32, ?_, ?_⟩
      · rw [hcov_q r hr, List.getElem?_eq_getElem (by rw [htmpl_s]; omega), hu_eq]
      · rw [m6_bv32_and_not1_toNat]; have := hws2_lt u hu.1; omega
    · rw [hdrop_s, hlhs]; exact xorK_gateK_def hi_lt hodd hnp_par hperm_all
  refine ⟨fun idx hidx => ?_, ?_⟩
  · rw [hpres_q idx (by omega), List.getElem?_set_ne (by rw [hcg1_eq]; omega),
      List.getElem?_set_ne (by omega)]
    exact hpres5 idx hidx
  · refine congGateSeqOk_append_gate (g_len := cur_g.toNat) (scr := scr5) (scr' := scr_q)
      (fun idx hidx => ?_) hseq5 ?_ (by rw [hcg_eq, Nat.add_mul]; omega)
    · rw [hpres_q idx (by omega), List.getElem?_set_ne (by rw [hcg1_eq]; omega),
        List.getElem?_set_ne (by omega)]
    · have har_m : congGateArity mword = k - 1 := by
        rw [hmword_eq]; rcases (by omega : k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl <;> decide
      exact .step hgate_at (by
        rw [h1_scr, Option.getD_some, har_m,
          show cur_g.toNat + 2 + (k - 1) = g_len + (i + 1) * (k + 1) by
            rw [hcg_eq, Nat.add_mul]; omega]
        exact .done)

private theorem xorK_distinct_j_step {ws : List (BitVec 32)} {j li : BitVec 32}
    (hjw : (j.setWidth 64).toNat < ws.length) (hj_lt : j.toNat < ws.length)
    (hdist : ∀ a < j.toNat, (ws[a]?.getD 0#32).toNat / 2 ≠ li.toNat / 2)
    (hc : (ws[(j.setWidth 64).toNat]'hjw >>> (1 : BitVec 32)) ≠ li >>> (1 : BitVec 32)) :
    ∀ a < j.toNat + 1, (ws[a]?.getD 0#32).toNat / 2 ≠ li.toNat / 2 := fun a ha => by
  by_cases haj : a = j.toNat
  · subst haj
    have hlj : (ws[(j.setWidth 64).toNat]'hjw).toNat / 2 =
        (ws[j.toNat]?.getD 0#32).toNat / 2 := by
      rw [list_getElem_congr (bv_zext32_toNat j) hjw hj_lt,
        List.getElem?_eq_getElem hj_lt, Option.getD_some]
    intro heq; apply hc; apply BitVec.eq_of_toNat_eq
    change (ws[(j.setWidth 64).toNat]'hjw >>> (1 : Nat)).toNat = (li >>> (1 : Nat)).toNat
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, Nat.pow_one, hlj, heq]
  · exact hdist a (by omega)

private theorem xorK_distinct_i_step {ws : List (BitVec 32)} {i : BitVec 32}
    (hiw : (i.setWidth 64).toNat < ws.length) (hi_lt : i.toNat < ws.length)
    (hdi : ∀ a b, a < b → b < i.toNat →
      (ws[a]?.getD 0#32).toNat / 2 ≠ (ws[b]?.getD 0#32).toNat / 2)
    (hdj : ∀ a < i.toNat,
      (ws[a]?.getD 0#32).toNat / 2 ≠ (ws[(i.setWidth 64).toNat]'hiw).toNat / 2) :
    ∀ a b, a < b → b < i.toNat + 1 →
      (ws[a]?.getD 0#32).toNat / 2 ≠ (ws[b]?.getD 0#32).toNat / 2 := fun a b hab hbi => by
  by_cases hbi' : b = i.toNat
  · subst hbi'
    have hli : ws[(i.setWidth 64).toNat]'hiw = ws[i.toNat]?.getD 0#32 := by
      rw [list_getElem_congr (bv_zext32_toNat i) hiw hi_lt,
        List.getElem?_eq_getElem hi_lt, Option.getD_some]
    rw [← hli]; exact hdj a hab
  · exact hdi a b hab (by omega)

private theorem xorK_tmp_set_step {tmp_q ws2 : List (BitVec 32)} {q mask val : BitVec 32}
    (hq_tmp : (q.setWidth 64).toNat < tmp_q.length)
    (hval : val.toNat = (ws2[q.toNat]?.getD 0#32).toNat ^^^ ((mask.toNat >>> q.toNat) &&& 1))
    (hcov : ∀ r < q.toNat, (tmp_q[r]?.getD 0#32).toNat =
      (ws2[r]?.getD 0#32).toNat ^^^ ((mask.toNat >>> r) &&& 1)) :
    ∀ r < q.toNat + 1, ((tmp_q.set (q.setWidth 64).toNat val)[r]?.getD 0#32).toNat =
      (ws2[r]?.getD 0#32).toNat ^^^ ((mask.toNat >>> r) &&& 1) := fun r hr => by
  by_cases hrq : r = q.toNat
  · subst hrq; rw [bv_zext32_toNat] at hq_tmp ⊢
    rw [List.getElem?_set_self hq_tmp, Option.getD_some, hval]
  · rw [List.getElem?_set_ne (by rw [bv_zext32_toNat]; exact Ne.symm hrq)]
    exact hcov r (by omega)

private theorem xorK_clause_map_eq {tmp_q ws2 : List (BitVec 32)} {k mask : Nat}
    (hcov : ∀ r < k, (tmp_q[r]?.getD 0#32).toNat =
      (ws2[r]?.getD 0#32).toNat ^^^ ((mask >>> r) &&& 1)) :
    ((List.range k).map fun j => (tmp_q[j]?.getD 0#32).toNat) = xorKClause ws2 k mask := by
  apply List.ext_getElem (by simp [xorKClause])
  intro r hr _; simp only [List.length_map, List.length_range] at hr
  simp only [List.getElem_map, List.getElem_range, xorKClause]; exact hcov r hr

private theorem xorK_k4_gates {F_cur : List (List Nat)} {s4 : FullState}
    {ws2 : List (BitVec 32)} {k len : Nat} (hk4 : k = 4) (hws24 : s4.scratch.work_stk2 = ws2)
    (hws2_lt : ∀ j < k, (ws2[j]?.getD 0#32).toNat < 2 * len)
    (hws_len : 4 ≤ s4.scratch.work_stk2.length)
    (hodd : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      xorEvalList α ((List.range k).map fun j => (ws2[j]?.getD 0#32).toNat) = true) :
    let l := fun q (hq : q < 4) => (s4.scratch.work_stk2[q]'(by omega)).toNat
    (l 0 (by omega) < 2 * len ∧ l 1 (by omega) < 2 * len ∧
     l 2 (by omega) < 2 * len ∧ l 3 (by omega) < 2 * len) ∧
    XorListGateDef (cnfOfClauses F_cur) (litNeg (l 0 (by omega)))
      [l 1 (by omega), l 2 (by omega), l 3 (by omega)] ∧
    XorListGateDef (cnfOfClauses F_cur) (litNeg (l 1 (by omega)))
      [l 0 (by omega), l 2 (by omega), l 3 (by omega)] ∧
    XorListGateDef (cnfOfClauses F_cur) (litNeg (l 2 (by omega)))
      [l 0 (by omega), l 1 (by omega), l 3 (by omega)] ∧
    XorListGateDef (cnfOfClauses F_cur) (litNeg (l 3 (by omega)))
      [l 0 (by omega), l 1 (by omega), l 2 (by omega)] := by
  have hws_idx : ∀ q (hq : q < 4),
      (s4.scratch.work_stk2[q]'(by omega)) = ws2[q]?.getD 0#32 := fun q hq => by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega), hws24,
      List.getElem?_eq_getElem (by rw [← hws24]; omega), Option.getD_some]
  have hodd4 : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α → xorEvalList α
      [(ws2[0]?.getD 0#32).toNat, (ws2[1]?.getD 0#32).toNat,
       (ws2[2]?.getD 0#32).toNat, (ws2[3]?.getD 0#32).toNat] = true := fun α hα => by
    have h := hodd α hα; rwa [hk4] at h
  obtain ⟨hd0, hd1, hd2, hd3⟩ := xorK_gate4_defs hodd4
  dsimp only
  rw [hws_idx 0 (by omega), hws_idx 1 (by omega), hws_idx 2 (by omega), hws_idx 3 (by omega)]
  exact ⟨⟨hws2_lt 0 (by omega), hws2_lt 1 (by omega), hws2_lt 2 (by omega),
    hws2_lt 3 (by omega)⟩, hd0, hd1, hd2, hd3⟩

private theorem xorK_k35_q_step {scr_q scr_h tmp_s : List (BitVec 32)}
    {cur_g : BitVec 64} {q : BitVec 32} (hq_tmp : (q.setWidth 64).toNat < tmp_s.length)
    (hq_nat : q.toNat < tmp_s.length)
    (hq_scr : (cur_g + 2#64 + q.setWidth 64).toNat < scr_q.length)
    (hcg_add : (cur_g + 2#64 + q.setWidth 64).toNat = cur_g.toNat + 2 + q.toNat)
    (hpres_q : ∀ idx < cur_g.toNat + 2, scr_q[idx]? = scr_h[idx]?)
    (hcov_q : ∀ r < q.toNat, scr_q[cur_g.toNat + 2 + r]? = tmp_s[r]?) :
    let scr' := scr_q.set (cur_g + 2#64 + q.setWidth 64).toNat
      (tmp_s[(q.setWidth 64).toNat]'hq_tmp)
    (∀ idx < cur_g.toNat + 2, scr'[idx]? = scr_h[idx]?) ∧
    (∀ r < q.toNat + 1, scr'[cur_g.toNat + 2 + r]? = tmp_s[r]?) := by
  refine ⟨fun idx hidx => ?_, fun r hr => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hpres_q idx hidx
  · by_cases hrq : r = q.toNat
    · subst hrq; rw [← hcg_add, List.getElem?_set_self hq_scr,
        list_getElem_congr (bv_zext32_toNat q) hq_tmp hq_nat, List.getElem?_eq_getElem hq_nat]
    · rw [List.getElem?_set_ne (by omega)]; exact hcov_q r (by omega)

private theorem xorK_k35_post_ok {maxA cur_vars scratch_cap tmp_len : Nat}
    {F_cur : List (List Nat)} {ws2 scr0 scr5 scr_q tmp_j tmp_s : List (BitVec 32)}
    {g_len cur_g : BitVec 64} {k neg_p i q lhs mword : BitVec 32}
    {hmw : mword = (1#32 <<< 28) ||| (k - 1#32)}
    (hmax4 : 4 ≤ maxA) (hk3 : 3 ≤ k.toNat) (hk5 : k.toNat ≤ 5) (hkcv : k.toNat ≤ cur_vars)
    (hi_lt : i.toNat < k.toNat) (hcg_eq : cur_g.toNat = g_len.toNat + i.toNat * (k.toNat + 1))
    (hcap_k : g_len.toNat + k.toNat * (k.toNat + 1) ≤ scratch_cap) (hsc : scratch_cap < 2 ^ 28)
    (hscr5l : scr5.length = scratch_cap) (hscrl_q : scr_q.length = scratch_cap)
    (htmpl_j : tmp_j.length = tmp_len) (htmpl_s : tmp_s.length = tmp_j.length)
    (hk1_le : k.toNat - 1 ≤ tmp_len) (hi_ws2 : (i.setWidth 64).toNat < ws2.length)
    (hws2_len : k.toNat ≤ ws2.length)
    (hws2_lt : ∀ j < k.toNat, (ws2[j]?.getD 0#32).toNat < 2 * cur_vars)
    (hodd : ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      xorEvalList α ((List.range k.toNat).map fun j => (ws2[j]?.getD 0#32).toNat) = true)
    (hnp_par : (neg_p &&& 1#32).toNat = (List.range k.toNat).foldl
      (fun acc j => acc ^^^ ((ws2[j]?.getD 0#32).toNat % 2)) 0)
    (hlhs : lhs = (ws2[(i.setWidth 64).toNat]'hi_ws2 &&& ~~~1#32) |||
      (1#32 ^^^ (neg_p &&& 1#32)))
    (hpres5 : ∀ idx < g_len.toNat, scr5[idx]? = scr0[idx]?)
    (hseq5 : CongGateSeqOk maxA F_cur cur_vars scr5 cur_g.toNat 0)
    (hpres_q : ∀ idx < cur_g.toNat + 2,
      scr_q[idx]? = ((scr5.set cur_g.toNat lhs).set (cur_g + 1#64).toNat mword)[idx]?)
    (hc_q : ¬q.toNat < (2 ^ 32 - (1 : BitVec 32).toNat + k.toNat) % 2 ^ 32)
    (hq_le : q.toNat ≤ k.toNat - 1)
    (hcov_q : ∀ r < q.toNat, scr_q[cur_g.toNat + 2 + r]? = tmp_s[r]?)
    (hperm_s : List.Perm (tmp_s.take (k - 1#32).toNat) (tmp_j.take (k - 1#32).toNat))
    (hperm_j : List.Perm ((List.range (k.toNat - 1)).map fun q => tmp_j[q]?.getD 0#32)
      (((List.range k.toNat).filter (· ≠ i.toNat)).map fun q => ws2[q]?.getD 0#32 &&& ~~~1#32)) :
    (cur_g + 2#64 + (k - 1#32).setWidth 64).toNat =
      g_len.toNat + (i.toNat + 1) * (k.toNat + 1) ∧
    (∀ idx < g_len.toNat, scr_q[idx]? = scr0[idx]?) ∧
    CongGateSeqOk maxA F_cur cur_vars scr_q
      (cur_g + 2#64 + (k - 1#32).setWidth 64).toNat 0 := by
  have hkm1 : (k - 1#32).toNat = k.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ k.toNat; omega))]; rfl
  have hkm1_alt : (2 ^ 32 - (1 : BitVec 32).toNat + k.toNat) % 2 ^ 32 = k.toNat - 1 := by
    have hsub : 2 ^ 32 - (1 : BitVec 32).toNat + k.toNat = 2 ^ 32 + (k.toNat - 1) := by
      have : (1 : BitVec 32).toNat = 1 := rfl; omega
    rw [hsub, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hq_eq : q.toNat = k.toNat - 1 := by omega
  have hi_mul0 : i.toNat * (k.toNat + 1) ≤ k.toNat * (k.toNat + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hmul_bd : (i.toNat + 1) * (k.toNat + 1) ≤ k.toNat * (k.toNat + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hadd_eq : (i.toNat + 1) * (k.toNat + 1) = i.toNat * (k.toNat + 1) + (k.toNat + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  have hcap_step : g_len.toNat + (i.toNat + 1) * (k.toNat + 1) ≤ scratch_cap := by omega
  have hcgr_eq : (cur_g + 2#64 + (k - 1#32).setWidth 64).toNat =
      g_len.toNat + (i.toNat + 1) * (k.toNat + 1) := by
    have hcg2_eq : (cur_g + 2#64).toNat = cur_g.toNat + 2 := by
      rw [BitVec.toNat_add, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hcg2_eq, bv_zext32_toNat, hkm1, Nat.mod_eq_of_lt (by omega)]; omega
  have hlhs_eq : lhs = (ws2[i.toNat]?.getD 0#32 &&& ~~~1#32) ||| (1#32 ^^^ (neg_p &&& 1#32)) := by
    have hli : ws2[(i.setWidth 64).toNat]'hi_ws2 = ws2[i.toNat]?.getD 0#32 := by
      rw [list_getElem_congr (bv_zext32_toNat i) hi_ws2 (by omega),
        List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hlhs, hli]
  have htake : tmp_j.take (k.toNat - 1) =
      (List.range (k.toNat - 1)).map fun q => tmp_j[q]?.getD 0#32 :=
    xorK_take_eq_range_map tmp_j (k.toNat - 1) (by omega)
  have hperm_j' : List.Perm (tmp_j.take (k - 1#32).toNat)
      (((List.range k.toNat).filter (· ≠ i.toNat)).map fun q => ws2[q]?.getD 0#32 &&& ~~~1#32) := by
    rw [hkm1, htake]; exact hperm_j
  have hperm_all : List.Perm (tmp_s.take (k.toNat - 1))
      (((List.range k.toNat).filter (· ≠ i.toNat)).map fun q => ws2[q]?.getD 0#32 &&& ~~~1#32) := by
    rw [← hkm1]; exact hperm_s.trans hperm_j'
  have ⟨hpres_next, hseq_next⟩ := xorK_emit_gate_post hmax4 hk3 hk5 hkcv rfl hi_lt
    hcg_eq hcap_step hsc hscr5l hscrl_q (by omega) (by omega) hws2_lt hodd hnp_par
    hlhs_eq hmw hpres5 hseq5 hpres_q (fun r hr => hcov_q r (by omega)) hperm_all
  exact ⟨hcgr_eq, hpres_next, by rwa [hcgr_eq]⟩

/-! ## 9. `full_cong_extract_xor_k_wp` (`Spec.fullCongExtractXorKSpec`) -/

/-- Canonical `Func.wp` proof for `full_cong_extract_xor_k`. -/
theorem full_cong_extract_xor_k_wp (Γ : Env)
    (hHasClK : Γ.Has "full_cong_has_clause_k" Spec.fullCongHasClauseKSpec)
    (hEmitXor4 : Γ.Has "full_cong_emit_xor4" Spec.fullCongEmitXor4Spec)
    (hSort : Γ.Has "full_sort_u32" fullSortU32Spec) :
    ∀ args m Q X, Spec.fullCongExtractXorKSpec args m Q X →
      Func.wp Γ full_cong_extract_xor_k_body args m Q X := by
  rintro ⟨h, k, neg_p, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, R, hmax4, hmax64, rfl, hlen, hw, hmk, hnd, hcl0, hk3, hk5, hkcv,
      hg_le, hg_cap, hseq0, hws2_lt, hnp_par, hent0, hm0, hQ⟩
  have hmx := c.hmaxv; have hsc := c.hscr; unfold dimacsBound at hmx hsc
  have hcv_le := hlen.core_ok.cur_vars_le; have htmpl := hlen.core_ok.tmp_len_arr
  have hwvl := hlen.core_ok.wvec_len; have hws2l := hlen.scratch_ok.work_stk2_len
  have hscrl := hlen.scratch_ok.scratch_buf_len
  let retS : ∀ m', (FullMem c s ⋆ R) m' → Q (g_len, ()) m' := fun m' hm' =>
    hQ g_len s m' hlen rfl rfl hmk (Nat.le_refl _) hg_le (fun _ _ => rfl) hseq0 hm'
  unfold Func.wp full_cong_extract_xor_k_body
  c0_hsplit; · c0_hsteps!; exact retS _ hm0
  clear hc; c0_hsplit; · c0_hsteps!; exact retS _ hm0
  clear hc; c0_hsplit; · c0_hsteps!; exact retS _ hm0
  clear hc; c0_hsplit; · c0_hsteps!; exact retS _ hm0
  have hcap_k := xorK_cap_ok hk3 hk5 hg_le hg_cap hsc hc; clear hc; c0_hsteps_nogrp
  refine LeanQbe.T.wp_loop_inv (ts := [i32, i32]) (fun (_par, i, ()) mi =>
      mi = m0 ∧ i.toNat ≤ k.toNat ∧ ∀ a b, a < b → b < i.toNat →
        (s.scratch.work_stk2[a]?.getD 0#32).toNat / 2 ≠
          (s.scratch.work_stk2[b]?.getD 0#32).toNat / 2)
    (fun (_par, i, ()) _ => k.toNat - i.toNat) (fun Jl hJl => by
      c0_hsteps!; exact hJl (0#32, 0#32, ()) m0 ⟨rfl, Nat.zero_le _,
        fun _ _ _ hb => by simp at hb⟩)
    (fun Jl (par, i, ()) mi ⟨hm_i, hi_le, hdist_i⟩ ihl => ?_)
  have hm0_i : (FullMem c s ⋆ R) mi := hm_i ▸ hm0
  c0_hsplit
  · have hi_lt : i.toNat < k.toNat := hc
    have hi_ws2 : (i.setWidth 64).toNat < s.scratch.work_stk2.length := by
      rw [bv_zext32_toNat]; omega
    let li := s.scratch.work_stk2[(i.setWidth 64).toNat]'hi_ws2
    have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
    clear hc; c0_hsteps_nogrp
    refine LeanQbe.T.wp_join_group (ts := [i32]) (fun (_next_par, ()) mj => mj = m0) ?_ ?_
    · rintro _ ⟨next_par, ⟨⟩⟩ mj hmj
      have hm0_j : (FullMem c s ⋆ R) mj := hmj ▸ hm0; c0_hsteps_nogrp
      refine LeanQbe.T.wp_loop_inv (ts := [i32])
        (fun (j, ()) mk => mk = m0 ∧ j.toNat ≤ i.toNat ∧
          ∀ a < j.toNat, (s.scratch.work_stk2[a]?.getD 0#32).toNat / 2 ≠ li.toNat / 2)
        (fun (j, ()) _ => i.toNat - j.toNat) (fun J2 hJ2 => by
          c0_hsteps!; exact hJ2 (0#32, ()) mj ⟨hmj, Nat.zero_le _, fun _ hb => by simp at hb⟩)
        (fun J2 (j, ()) mk ⟨hmk', hj_le, hdist_j⟩ ihj => ?_)
      have hm0_k : (FullMem c s ⋆ R) mk := hmk' ▸ hm0; c0_hsplit
      · have hj_lt : j.toNat < i.toNat := hc
        have hj_ws2 : (j.setWidth 64).toNat < s.scratch.work_stk2.length := by
          rw [bv_zext32_toNat]; omega
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
        clear hc; c0_hsplit
        · c0_hsteps!; exact retS mk (hmk' ▸ hm0)
        · c0_hsteps!; refine ihj (j + 1#32, ()) mk (by dsimp only; omega)
            ⟨hmk', by omega, by rw [hj1]; exact xorK_distinct_j_step hj_ws2 (by omega) hdist_j hc⟩
      · have hj_ge : ¬ j.toNat < i.toNat := hc
        c0_hsteps!; refine ihl (next_par, i + 1#32, ()) mk (by dsimp only; omega)
          ⟨hmk', by omega, ?_⟩
        rw [hi1]; exact xorK_distinct_i_step hi_ws2 (by omega)
          hdist_i (fun a ha => hdist_j a (by omega))
    · intro J1 hJ1; c0_hsteps_nogrp; c0_hsplit
      · c0_hsteps!; exact hJ1 (_, ()) mi hm_i
      · c0_hsteps!; exact hJ1 (_, ()) mi hm_i
  · have hi_eq : i.toNat = k.toNat := by omega
    have hws2_nodup : ∀ a b, a < b → b < k.toNat → (s.scratch.work_stk2[a]?.getD 0#32).toNat / 2
        ≠ (s.scratch.work_stk2[b]?.getD 0#32).toNat / 2 := by simpa [hi_eq] using hdist_i
    clear hc; c0_hsteps_nogrp
    refine LeanQbe.T.wp_loop_inv (ts := [i32]) (fun (i2, ()) m2 => m2 = m0 ∧ i2.toNat ≤ k.toNat)
      (fun (i2, ()) _ => k.toNat - i2.toNat)
      (fun J2 hJ2 => by c0_hsteps!; exact hJ2 (0#32, ()) mi ⟨hm_i, Nat.zero_le _⟩)
      (fun J2 (i2, ()) m2 ⟨hm2, hi2_le⟩ ih2 => ?_)
    have hm0_2 : (FullMem c s ⋆ R) m2 := hm2 ▸ hm0; c0_hsplit
    · have hi2_lt : i2.toNat < k.toNat := hc
      have hi2_ws2 : (i2.setWidth 64).toNat < s.scratch.work_stk2.length := by
        rw [bv_zext32_toNat]; omega
      have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := by bv_omega
      clear hc; c0_hsteps_nogrp
      refine LeanQbe.T.wp_join_group (ts := []) (fun _ m2' => m2' = m0) (fun _ ⟨⟩ m2' hm2' => by
          c0_hsteps!; exact ih2 (i2 + 1#32, ()) m2' (by dsimp only; omega) ⟨hm2', by omega⟩)
        (fun Jskip hJskip => by
          c0_hsteps_nogrp; try c0_hsplit
          all_goals (try clear hc; c0_hsteps_nogrp; try c0_hsplit)
          all_goals first | exact hJskip () m2 hm2 | (c0_hsteps!; exact retS m2 (hm2 ▸ hm0)))
    · clear hc; c0_hsteps_nogrp
      refine LeanQbe.T.wp_loop_inv (ts := [i32]) (fun (i3, ()) m3 => m3 = m0 ∧ i3.toNat ≤ k.toNat)
        (fun (i3, ()) _ => k.toNat - i3.toNat)
        (fun J3 hJ3 => by c0_hsteps!; exact hJ3 (0#32, ()) m2 ⟨hm2, Nat.zero_le _⟩)
        (fun J3 (i3, ()) m3 ⟨hm3, hi3_le⟩ ih3 => ?_)
      have hm0_3 : (FullMem c s ⋆ R) m3 := hm3 ▸ hm0; c0_hsplit
      · have hi3_lt : i3.toNat < k.toNat := hc
        have hi3_ws2 : (i3.setWidth 64).toNat < s.scratch.work_stk2.length := by
          rw [bv_zext32_toNat]; omega
        let w3 := s.scratch.work_stk2[(i3.setWidth 64).toNat]'hi3_ws2
        have hw3_lt : w3.toNat < 2 * s.core.cur_vars := by
          have : w3 = s.scratch.work_stk2[i3.toNat]?.getD 0#32 := by
            dsimp only [w3]; rw [list_getElem_congr (bv_zext32_toNat i3) hi3_ws2 (by omega),
              List.getElem?_eq_getElem (by omega), Option.getD_some]
          rw [this]; exact hws2_lt _ hi3_lt
        rcases xorK_wvec_bounds hw3_lt hcv_le hwvl hlen.scratch_ok.work_stk1_len with
          ⟨hwv_pos, hwv_neg, hw1_x1, hw1_o1, hwv_x1, hwv_o1⟩
        have hw1_x1' : ((s.scratch.work_stk2[(i3.setWidth 64).toNat]'hi3_ws2 &&& ~~~1#32 ^^^
            1#32).setWidth 64).toNat < s.scratch.work_stk1.length := hw1_x1
        have hw1_o1' : (((s.scratch.work_stk2[(i3.setWidth 64).toNat]'hi3_ws2 &&& ~~~1#32 |||
            1#32) ^^^ 1#32).setWidth 64).toNat < s.scratch.work_stk1.length := hw1_o1
        have hi3_1 : (i3 + 1#32).toNat = i3.toNat + 1 := by bv_omega
        clear hc; c0_hsteps_nogrp
        refine LeanQbe.T.wp_join_group (ts := [i32]) (fun _ m3a => m3a = m0) ?_ (fun J3a hJ3a => by
          c0_hsplit <;> (c0_hsteps!; exact hJ3a (_, ()) m3 hm3))
        rintro _ ⟨_, ⟨⟩⟩ m3a hm3a; have hm0_3a : (FullMem c s ⋆ R) m3a := hm3a ▸ hm0
        c0_hsteps_nogrp
        refine LeanQbe.T.wp_join_group (ts := [i32]) (fun _ m3b => m3b = m0) ?_ (fun J3b hJ3b => by
          c0_hsplit <;> (c0_hsteps!; exact hJ3b (_, ()) m3a hm3a))
        rintro _ ⟨_, ⟨⟩⟩ m3b hm3b; have hm0_3b : (FullMem c s ⋆ R) m3b := hm3b ▸ hm0
        c0_hsplit; · c0_hsteps!; exact retS m3b (hm3b ▸ hm0)
        clear hc; c0_hsplit; · c0_hsteps!; exact retS m3b (hm3b ▸ hm0)
        c0_hsteps!; exact ih3 (i3 + 1#32, ()) m3b (by dsimp only; omega) ⟨hm3b, by omega⟩
      · clear hc -- Phase 4: mask loop `mask = 1 ..< 2^k`
        have hlim_shl : (1 : BitVec 32).toNat * 2 ^ (k.toNat % 32) % 2 ^ 32 = 2 ^ k.toNat := by
          rcases (by omega : k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 5) with hk | hk | hk <;>
            simp [hk]
        have hw_of : ∀ (cr : FullCoreState), { cr with tmp := s.core.tmp, lit_mark :=
            s.core.lit_mark } = s.core → FullWitnessInv c F0 F_cur cr := fun cr hcr => by
          have := fullWitnessInv_with_tmp_lm hw cr.tmp cr.lit_mark; rwa [← hcr] at this
        c0_hsteps_nogrp
        refine LeanQbe.T.wp_loop_inv (ts := [i32])
          (fun (mask, ()) m4 => 1 ≤ mask.toNat ∧ mask.toNat ≤ 2 ^ k.toNat ∧
            ∃ s4 : FullState, s4.LengthsOk c ∧
              { s4.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core ∧
              s4.scratch = s.scratch ∧ FullLitMarksClear c s4 ∧
              (∀ mc < mask.toNat, xorKBitParity k.toNat mc = 0 → (cnfOfClauses F_cur).EntailsClause
                (cnfClause (xorKClause s.scratch.work_stk2 k.toNat mc))) ∧ (FullMem c s4 ⋆ R) m4)
          (fun (mask, ()) _ => 2 ^ k.toNat - mask.toNat)
          (fun J4 hJ4 => by c0_hsteps!; refine hJ4 (1#32, ()) m3 ⟨by decide, by
            rcases (by omega : k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 5) with hk | hk | hk <;>
              simp [hk], s, hlen, rfl, rfl, hmk, fun mc hmc _ => by
              have hmz : mc = 0 := by have h1 : (1#32 : BitVec 32).toNat = 1 := rfl; omega
              subst hmz; simpa [xorKClause, Nat.zero_shiftRight, Nat.zero_and] using hent0,
            hm3 ▸ hm0⟩)
          (fun J4 (mask, ()) m4 ⟨hm_ge1, hm_le, s4, hl4, hc4, hs4, hmk4, heven_i, hm4⟩ ih4 => ?_)
        have hw4 := hw_of s4.core hc4
        have hcl04 : s4.core.cur_level = 0 := by
          simpa [hcl0] using congrArg FullCoreState.cur_level hc4
        have hnd4 := fullArenaVarsNodup_of_eq hnd (by simpa using congrArg FullCoreState.arena hc4)
          (by simpa using congrArg FullCoreState.arena_len hc4)
        have hcv4 : s4.core.cur_vars = s.core.cur_vars := by
          simpa using congrArg FullCoreState.cur_vars hc4
        have hws24 : s4.scratch.work_stk2 = s.scratch.work_stk2 := by rw [hs4]
        have hws24_len : s4.scratch.work_stk2.length = 2 * c.max_vars := by rw [hws24, hws2l]
        c0_hsplit
        · have hm_lt : mask.toNat < 2 ^ k.toNat := by rw [← hlim_shl]; exact hc
          have hm1 : (mask + 1#32).toNat = mask.toNat + 1 := by bv_omega
          clear hc; c0_hsteps_nogrp
          refine LeanQbe.T.wp_loop_inv (ts := [i32, i32]) (fun (odd, j, ()) m4a =>
              m4a = m4 ∧ j.toNat ≤ k.toNat ∧ odd.toNat = xorKBitParity j.toNat mask.toNat)
            (fun (_odd, j, ()) _ => k.toNat - j.toNat) (fun J4a hJ4a => by
              c0_hsteps!; exact hJ4a (0#32, 0#32, ()) m4 ⟨rfl, Nat.zero_le _, rfl⟩)
            (fun J4a (odd, j, ()) m4a ⟨hm4a, hj_le, hodd_eq⟩ ih4a => ?_)
          c0_hsplit
          · have hj_lt : j.toNat < k.toNat := hc
            have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
            clear hc; c0_hsteps!
            refine ih4a (odd ^^^ ((mask >>> (j.toNat % 32)) &&& 1), j + 1#32, ()) m4a
              (by dsimp only; omega) ⟨hm4a, by omega, ?_⟩
            rw [hj1, xorKBitParity, BitVec.toNat_xor, BitVec.toNat_and,
              show (1 : BitVec 32).toNat = 1 from rfl, BitVec.toNat_ushiftRight,
              Nat.mod_eq_of_lt (by omega), hodd_eq]
          · have hj_eq : j.toNat = k.toNat := by omega
            clear hc; c0_hsteps_nogrp
            refine LeanQbe.T.wp_join_group (ts := [i32])
              (fun _ m4b => ∃ s5 : FullState, s5.LengthsOk c ∧
                { s5.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core ∧
                s5.scratch = s.scratch ∧ FullLitMarksClear c s5 ∧
                (xorKBitParity k.toNat mask.toNat = 0 → (cnfOfClauses F_cur).EntailsClause
                  (cnfClause (xorKClause s.scratch.work_stk2 k.toNat mask.toNat))) ∧
                (FullMem c s5 ⋆ R) m4b) ?_ ?_
            · rintro _ ⟨_, ⟨⟩⟩ m4b ⟨s5, hl5, hc5, hs5, hmk5, hnew, hm5⟩
              c0_hsteps!; refine ih4 (mask + 1#32, ()) m4b (by dsimp only; omega)
                ⟨by omega, by omega, s5, hl5, hc5, hs5, hmk5, fun mc hmc hpar => by
                  by_cases hmeq : mc = mask.toNat
                  · subst hmeq; exact hnew hpar
                  · exact heven_i mc (by omega) hpar, hm5⟩
            · intro Jnext hJnext; c0_hsplit
              · have hpar0 : xorKBitParity k.toNat mask.toNat = 0 := by
                  rw [← hj_eq, ← hodd_eq]; exact congrArg BitVec.toNat hc
                clear hc; c0_hsteps_nogrp
                refine LeanQbe.T.wp_loop_inv (ts := [i32])
                  (fun (q, ()) m4c => q.toNat ≤ k.toNat ∧
                    ∃ tmp_q : List (BitVec 32), tmp_q.length = c.max_vars ∧
                      (∀ r < q.toNat, (tmp_q[r]?.getD 0#32).toNat =
                        ((s.scratch.work_stk2[r]?.getD 0#32).toNat ^^^
                          ((mask.toNat >>> r) &&& 1))) ∧
                      (FullMem c { s4 with core := { s4.core with tmp := tmp_q } } ⋆ R) m4c)
                  (fun (q, ()) _ => k.toNat - q.toNat)
                  (fun J4b hJ4b => by c0_hsteps!; exact hJ4b (0#32, ()) m4a ⟨Nat.zero_le _,
                    s4.core.tmp, hl4.core_ok.tmp_len_arr, fun _ hr => by simp at hr, hm4a ▸ hm4⟩)
                  (fun J4b (q, ()) m4c ⟨hq_le, tmp_q, htmpl_q, hcov_q, hm4c⟩ ih4b => ?_)
                c0_hsplit
                · have hq_lt : q.toNat < k.toNat := hc
                  have hq_ws2 : (q.setWidth 64).toNat < s4.scratch.work_stk2.length := by
                    rw [bv_zext32_toNat, hws24]; omega
                  have hq_tmp : (q.setWidth 64).toNat < tmp_q.length := by
                    rw [bv_zext32_toNat]; omega
                  have hq1 : (q + 1#32).toNat = q.toNat + 1 := by bv_omega
                  let val := s4.scratch.work_stk2[(q.setWidth 64).toNat]'hq_ws2 ^^^
                    ((mask >>> (q.toNat % 32)) &&& 1#32)
                  let tmp_q' := tmp_q.set (q.setWidth 64).toNat val
                  have hws_q : s4.scratch.work_stk2[(q.setWidth 64).toNat]'hq_ws2 =
                      s.scratch.work_stk2[q.toNat]?.getD 0#32 := by
                    rw [← Option.some_inj, ← List.getElem?_eq_getElem hq_ws2, hws24,
                      bv_zext32_toNat, List.getElem?_eq_getElem (by omega), Option.getD_some]
                  have hval_eq : val.toNat = (s.scratch.work_stk2[q.toNat]?.getD 0#32).toNat ^^^
                      ((mask.toNat >>> q.toNat) &&& 1) := by
                    simp only [val, hws_q, BitVec.toNat_xor, BitVec.toNat_and,
                      BitVec.toNat_ushiftRight, show (1#32 : BitVec 32).toNat = 1 from rfl]
                    rw [Nat.mod_eq_of_lt (by omega)]
                  clear hc; c0_hsteps!
                  refine ih4b (q + 1#32, ()) m (by dsimp only; omega) ⟨by omega, tmp_q',
                    by simp [tmp_q', htmpl_q],
                    (by rw [hq1]; exact xorK_tmp_set_step hq_tmp hval_eq hcov_q),
                    by simpa [tmp_q', val, bv_zext32_toNat] using hm⟩
                · have h_mask : q.toNat = k.toNat := by omega
                  let s4t : FullState := { s4 with core := { s4.core with tmp := tmp_q } }
                  have hc4t : { s4t.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } =
                      s.core := by dsimp only [s4t]; simpa using hc4
                  have ⟨htmp_lt, htmp_nd⟩ := xorK_tmp_bounds (fun r hr => hcov_q r (by omega))
                    hws2_lt hws2_nodup
                  clear hc; c0_hsteps_nogrp
                  refine wp_call_of_spec _ _ (hHasClK _ _ _ _ ⟨c, F0, F_cur, s4t, R, rfl,
                    ⟨{ hl4.core_ok with tmp_len_arr := htmpl_q }, hl4.scratch_ok⟩,
                    hw_of s4t.core hc4t, hmk4, fullArenaVarsNodup_of_eq hnd
                      (by simpa using congrArg FullCoreState.arena hc4t)
                      (by simpa using congrArg FullCoreState.arena_len hc4t),
                    hcl04, hk3, hk5, by rw [hcv4]; exact hkcv, by rw [hcv4]; exact htmp_lt,
                    htmp_nd, hm4c, fun ok s5 m5 hl5 hc5 hs5 hmk5 hent5 hm5 => ?_⟩)
                  have hc5_eq : { s5.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } =
                      s.core := by simpa [s4t] using (congrArg (fun cr : FullCoreState =>
                    { cr with tmp := s.core.tmp, lit_mark := s.core.lit_mark }) hc5).trans hc4t
                  have hs5_eq : s5.scratch = s.scratch := hs5.trans hs4
                  c0_hsplit
                  · c0_hsteps!; refine hJnext (_, ()) m5 ⟨s5, hl5, hc5_eq, hs5_eq, hmk5, fun _ => by
                      rw [← xorK_clause_map_eq (fun r hr => hcov_q r (by omega))]; exact hent5 hc,
                      hm5⟩
                  · c0_hsteps!; exact hQ g_len s5 m5 hl5 hc5_eq (by rw [hs5_eq]) hmk5
                      (Nat.le_refl _) hg_le (by rw [hs5_eq]; exact fun _ _ => rfl)
                      (by rw [hs5_eq]; exact hseq0) hm5
              · have hne0 : xorKBitParity k.toNat mask.toNat ≠ 0 := fun hpar => by
                  apply hc; apply BitVec.eq_of_toNat_eq; rw [hodd_eq, hj_eq]; exact hpar
                c0_hsteps!; exact hJnext (_, ()) m4a ⟨s4, hl4, hc4, hs4, hmk4,
                  fun h => absurd h hne0, hm4a ▸ hm4⟩
        · have hm_eq : mask.toNat = 2 ^ k.toNat := by rw [← hlim_shl]; omega
          have hodd := xorK_eval_odd_of_even_clauses fun mc hmc => heven_i mc (by omega)
          have hscr4 : s4.scratch.scratch_buf = s.scratch.scratch_buf := by rw [hs4]
          have hws24_b : ∀ n < 4, (BitVec.ofNat 64 n).toNat < s4.scratch.work_stk2.length :=
            fun n hn => by
              rw [hws24_len]; change n % 2 ^ 64 < _; rw [Nat.mod_eq_of_lt (by omega)]; omega
          have h0_4 := hws24_b 0 (by omega); have h1_4 := hws24_b 1 (by omega)
          have h2_4 := hws24_b 2 (by omega); have h3_4 := hws24_b 3 (by omega)
          clear hc; c0_hsteps_nogrp; c0_hsplit
          · have hk4 : k.toNat = 4 := congrArg BitVec.toNat hc
            have hg20 : g_len.toNat + 20 ≤ g_cap.toNat := by rw [hk4] at hcap_k; omega
            have ⟨⟨hl0, hl1, hl2, hl3⟩, hd0, hd1, hd2, hd3⟩ :=
              xorK_k4_gates hk4 hws24 hws2_lt (by rw [hws24, hws2l]; omega) hodd
            let R4 := ArrayField.scratch_buf.rest c s4 ⋆ R; clear hc; c0_hsteps_nogrp
            refine wp_call_of_spec _ _ (hEmitXor4 _ _ _ _ ⟨maxA, F_cur, s.core.cur_vars,
              s.scratch.scratch_buf, R4, by omega, hmax64, hl0, hl1, hl2, hl3, by omega,
              by change g_len.toNat + 5 ≤ _; omega, by omega, hd0, hseq0,
              by have h1 := focus_full_scratch_buf hm4; rwa [hscr4] at h1,
              fun scr1 m1 hl1' hp1 hs1 hm1 => ?_⟩)
            have hg5 : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
            refine wp_call_of_spec _ _ (hEmitXor4 _ _ _ _ ⟨maxA, F_cur, s.core.cur_vars, scr1,
              R4, by omega, hmax64, hl1, hl0, hl2, hl3, by omega,
              by change (g_len + 5#64).toNat + 5 ≤ scr1.length; omega, by omega, hd1,
              by dsimp only [Arg.val] at hs1 ⊢; rwa [hg5], hm1,
              fun scr2 m2 hl2' hp2 hs2 hm2 => ?_⟩)
            have hg10 : (g_len + 5#64 + 5#64).toNat = g_len.toNat + 10 := by bv_omega
            refine wp_call_of_spec _ _ (hEmitXor4 _ _ _ _ ⟨maxA, F_cur, s.core.cur_vars, scr2,
              R4, by omega, hmax64, hl2, hl0, hl1, hl3, by omega,
              by change (g_len + 5#64 + 5#64).toNat + 5 ≤ scr2.length; omega, by omega, hd2,
              by dsimp only [Arg.val] at hs2 ⊢; rw [hg10]; rw [hg5] at hs2; exact hs2, hm2,
              fun scr3 m3 hl3' hp3 hs3 hm3 => ?_⟩)
            have hg15 : (g_len + 5#64 + 5#64 + 5#64).toNat = g_len.toNat + 15 := by bv_omega
            refine wp_call_of_spec _ _ (hEmitXor4 _ _ _ _ ⟨maxA, F_cur, s.core.cur_vars, scr3,
              R4, by omega, hmax64, hl3, hl0, hl1, hl2, by omega,
              by change (g_len + 5#64 + 5#64 + 5#64).toNat + 5 ≤ scr3.length; omega, by omega,
              hd3, by dsimp only [Arg.val] at hs3 ⊢; rw [hg15]; rw [hg10] at hs3; exact hs3, hm3,
              fun scr4 m4e hl4' hp4 hs4_seq hm4e => ?_⟩)
            have hg20' : (g_len + 5#64 + 5#64 + 5#64 + 5#64).toNat = g_len.toNat + 20 := by bv_omega
            dsimp only [Arg.val] at hp1 hp2 hp3 hp4 hs4_seq; rw [hg15] at hs4_seq; c0_hsteps!
            exact hQ (g_len + 5#64 + 5#64 + 5#64 + 5#64) { s4 with scratch := { s4.scratch with
              scratch_buf := scr4 } } m4e ⟨hl4.core_ok, { hl4.scratch_ok with
              scratch_buf_len := by dsimp only; rw [hl4', hl3', hl2', hl1', hscrl] }⟩ hc4
              (by dsimp only; rw [hs4]) hmk4 (by change g_len.toNat ≤ _; rw [hg20']; omega)
              (by change _ ≤ g_cap.toNat; rw [hg20']; omega) (fun idx hidx => by
                rw [hp4 idx (by omega), hp3 idx (by omega), hp2 idx (by omega), hp1 idx hidx])
              (by rw [hg20', show g_len.toNat + 20 = g_len.toNat + 15 + 5 by omega]
                  exact hs4_seq) (unfocus_full_scratch_buf hm4e)
          · have hkm1 : (k - 1#32).toNat = k.toNat - 1 := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ k.toNat; omega))]; rfl
            clear hc; c0_hsteps_nogrp
            refine LeanQbe.T.wp_loop_inv (ts := [i64, i32]) (fun (cur_g, i, ()) m5 =>
                i.toNat ≤ k.toNat ∧ cur_g.toNat = g_len.toNat + i.toNat * (k.toNat + 1) ∧
                ∃ s5 : FullState, s5.LengthsOk c ∧
                  { s5.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core ∧
                  { s5.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch ∧
                  FullLitMarksClear c s5 ∧ (∀ idx < g_len.toNat,
                    s5.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) ∧
                  CongGateSeqOk maxA F_cur s.core.cur_vars s5.scratch.scratch_buf cur_g.toNat 0 ∧
                  (FullMem c s5 ⋆ R) m5) (fun (_cur_g, i, ()) _ => k.toNat - i.toNat)
              (fun J5 hJ5 => by c0_hsteps!; exact hJ5 (g_len, 0#32, ()) m4 ⟨Nat.zero_le _, by simp,
                s4, hl4, hc4, by rw [hs4], hmk4, fun _ _ => by rw [hscr4], by rwa [hscr4], hm4⟩)
              (fun J5 (cur_g, i, ()) m5 ⟨hi_le, hcg_eq, s5, hl5, hc5, hs5, hmk5, hpres5, hseq5,
                hm5⟩ ih5 => ?_)
            have hws25 : s5.scratch.work_stk2 = s.scratch.work_stk2 := by
              simpa using congrArg FullScratch.work_stk2 hs5
            have hscr5l := hl5.scratch_ok.scratch_buf_len; c0_hsplit
            · have hi_lt : i.toNat < k.toNat := hc
              have hi_ws2 : (i.setWidth 64).toNat < s5.scratch.work_stk2.length := by
                rw [bv_zext32_toNat, hws25]; omega
              have hi_add_bd : i.toNat * (k.toNat + 1) + (k.toNat + 1) ≤ k.toNat * (k.toNat + 1) :=
                by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              have hcg0 : cur_g.toNat < s5.scratch.scratch_buf.length := by omega
              have hcg1 : (cur_g + 1#64).toNat < s5.scratch.scratch_buf.length := by
                have : (cur_g + 1#64).toNat = cur_g.toNat + 1 := by bv_omega
                omega
              let lhs := (s5.scratch.work_stk2[(i.setWidth 64).toNat]'hi_ws2 &&& ~~~1#32) |||
                (1#32 ^^^ (neg_p &&& 1#32))
              let scr_h := (s5.scratch.scratch_buf.set cur_g.toNat lhs).set
                (cur_g + 1#64).toNat ((1#32 <<< 28) ||| (k - 1#32))
              let s5h : FullState := { s5 with scratch := { s5.scratch with scratch_buf := scr_h } }
              have hs5hl : s5h.LengthsOk c := fidScr_lengthsOk hl5 (by simp [scr_h, hscr5l])
              clear hc; c0_hsteps_nogrp
              let inv5a : Tup Val [i32, i32] → Mem 64 → Prop := fun (cnt, j, ()) m5a =>
                j.toNat ≤ k.toNat ∧ cnt.toNat ≤ j.toNat ∧ cnt.toNat ≤ k.toNat - 1 ∧
                (i.toNat < j.toNat → cnt.toNat = j.toNat - 1) ∧
                (j.toNat ≤ i.toNat → cnt.toNat = j.toNat) ∧
                ∃ tmp_j : List (BitVec 32), tmp_j.length = c.max_vars ∧
                  List.Perm ((List.range cnt.toNat).map fun q => tmp_j[q]?.getD 0#32)
                    (((List.range j.toNat).filter (· ≠ i.toNat)).map fun q =>
                      s.scratch.work_stk2[q]?.getD 0#32 &&& ~~~1#32) ∧
                  (FullMem c { s5h with core := { s5h.core with tmp := tmp_j } } ⋆ R) m5a
              refine LeanQbe.T.wp_loop_inv (ts := [i32, i32]) inv5a
                (fun (_cnt, j, ()) _ => k.toNat - j.toNat)
                (fun J5a hJ5a => by c0_hsteps!; exact hJ5a (0#32, 0#32, ()) m ⟨Nat.zero_le _,
                  Nat.zero_le _, Nat.zero_le _, fun h => by simp at h, fun _ => rfl,
                  s5h.core.tmp, hl5.core_ok.tmp_len_arr, by simp, hm⟩)
                (fun J5a (cnt, j, ()) m5a ⟨hj_le, hcnt_j, hcnt_km1, hgt, hle, tmp_j, htmpl_j,
                  hperm_j, hm5a⟩ ih5a => ?_)
              c0_hsplit
              · have hj_lt : j.toNat < k.toNat := hc
                have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                clear hc; c0_hsteps_nogrp
                refine LeanQbe.T.wp_join_group (ts := [i32])
                  (fun (cnt', ()) m5a' => inv5a (cnt', j + 1#32, ()) m5a')
                  (fun _ ⟨cnt', ⟨⟩⟩ m5a' h' => by
                    c0_hsteps!; exact ih5a (cnt', j + 1#32, ()) m5a' (by dsimp only; omega) h') ?_
                intro Jj hJj; c0_hsplit
                · have hne : j.toNat ≠ i.toNat := fun heq => hc (BitVec.eq_of_toNat_eq heq)
                  have hcnt_lt : cnt.toNat < k.toNat - 1 := by
                    by_cases j.toNat < i.toNat <;> first | (have := hle (by omega); omega) |
                      (have := hgt (by omega); omega)
                  have hcnt_tmp : (cnt.setWidth 64).toNat < tmp_j.length := by
                    rw [bv_zext32_toNat]; omega
                  have hj_ws2 : (j.setWidth 64).toNat < s5h.scratch.work_stk2.length := by
                    rw [bv_zext32_toNat]; dsimp only [s5h]; rw [hws25]; omega
                  have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by bv_omega
                  let tmp_j' := tmp_j.set (cnt.setWidth 64).toNat
                    (s5h.scratch.work_stk2[(j.setWidth 64).toNat]'hj_ws2 &&& ~~~1#32)
                  have hws_j : s5h.scratch.work_stk2[(j.setWidth 64).toNat]'hj_ws2 =
                      s.scratch.work_stk2[j.toNat]'(by rw [hws2l]; omega) :=
                    Option.some.inj (by simp only [← List.getElem?_eq_getElem, s5h, hws25,
                      bv_zext32_toNat])
                  clear hc; c0_hsteps!
                  refine hJj (cnt + 1#32, ()) m ⟨by rw [hj1]; omega, by rw [hcnt1, hj1]; omega,
                    by rw [hcnt1]; omega,
                    fun h => by rw [hcnt1, hj1]; have := hgt (by rw [hj1] at h; omega); omega,
                    fun h => by rw [hcnt1, hj1]; have := hle (by rw [hj1] at h; omega); omega,
                    tmp_j', by simp [tmp_j', htmpl_j], ?_,
                    by simpa [tmp_j', bv_zext32_toNat] using hm⟩
                  rw [hcnt1, hj1]; dsimp only [tmp_j']; rw [bv_zext32_toNat, hws_j]
                  exact xorK_perm_set_step (cnt := cnt.toNat) (j := j.toNat) (i := i.toNat)
                    (by omega) (by rw [hws2l]; omega) hperm_j hne
                · have heq : j.toNat = i.toNat := congrArg BitVec.toNat (by simpa using hc)
                  c0_hsteps!; refine hJj (cnt, ()) m5a ⟨by rw [hj1]; omega, by rw [hj1]; omega,
                    hcnt_km1, fun _ => by rw [hj1]; have := hle (by omega); omega,
                    fun h => by rw [hj1] at h; omega, tmp_j, htmpl_j, ?_, hm5a⟩
                  rw [hj1, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
                  simpa [heq] using hperm_j
              · have hj_eq : j.toNat = k.toNat := by omega
                have hcnt_eq : cnt.toNat = k.toNat - 1 := by
                  have := hgt (by rw [hj_eq]; exact hi_lt); omega
                let s5t : FullState := { s5h with core := { s5h.core with tmp := tmp_j } }
                have hk1_len : (k - 1#32).toNat ≤ tmp_j.length := by omega
                clear hc; c0_hsteps_nogrp
                refine wp_call_of_spec _ _ (hSort _ _ _ _ ⟨tmp_j, ArrayField.tmp.rest c s5t ⋆ R,
                  hk1_len, focus_full_tmp hm5a, fun tmp_s m5b htmpl_s hperm_s _ hm5b => ?_⟩)
                let s5s : FullState := { s5t with core := { s5t.core with tmp := tmp_s } }
                have hm5b' := unfocus_full_tmp hm5b; c0_hsteps_nogrp
                refine LeanQbe.T.wp_loop_inv (ts := [i32])
                  (fun (q, ()) m5c => q.toNat ≤ k.toNat - 1 ∧
                    ∃ scr_q : List (BitVec 32), scr_q.length = c.scratch_cap ∧
                      (∀ idx < cur_g.toNat + 2, scr_q[idx]? = scr_h[idx]?) ∧
                      (∀ r < q.toNat, scr_q[cur_g.toNat + 2 + r]? = tmp_s[r]?) ∧
                      (FullMem c { s5s with scratch := { s5s.scratch with scratch_buf := scr_q } }
                        ⋆ R) m5c) (fun (q, ()) _ => k.toNat - 1 - q.toNat)
                  (fun J5b hJ5b => by c0_hsteps!; exact hJ5b (0#32, ()) m5b ⟨Nat.zero_le _, scr_h,
                    by simp [scr_h, hscr5l], fun _ _ => rfl, fun _ h => by simp at h, hm5b'⟩)
                  (fun J5b (q, ()) m5c ⟨hq_le, scr_q, hscrl_q, hpres_q, hcov_q, hm5c⟩ ih5b => ?_)
                c0_hsplit
                · have hq_lt : q.toNat < k.toNat - 1 := by rw [← hkm1]; exact hc
                  have hq_tmp : (q.setWidth 64).toNat < tmp_s.length := by
                    rw [bv_zext32_toNat, htmpl_s, htmpl_j]; omega
                  have hcg_add : (cur_g + 2#64 + q.setWidth 64).toNat = cur_g.toNat + 2 + q.toNat
                      := by
                    have : (cur_g + 2#64).toNat = cur_g.toNat + 2 := by bv_omega
                    rw [BitVec.toNat_add, this, bv_zext32_toNat, Nat.mod_eq_of_lt (by omega)]
                  have hq1 : (q + 1#32).toNat = q.toNat + 1 := by bv_omega
                  have ⟨hp_q, hc_q⟩ := xorK_k35_q_step hq_tmp (by omega) (by omega) hcg_add
                    hpres_q hcov_q
                  clear hc; c0_hsteps!; refine ih5b (q + 1#32, ()) m (by dsimp only; omega)
                    ⟨by omega, _, by simp [hscrl_q], hp_q, (by rw [hq1]; exact hc_q),
                      by simpa [bv_zext32_toNat] using hm⟩
                · have hi_ws2' : (i.setWidth 64).toNat < s.scratch.work_stk2.length := by
                    rw [← hws25]; exact hi_ws2
                  have hwi : s5.scratch.work_stk2[(i.setWidth 64).toNat]'hi_ws2 =
                      s.scratch.work_stk2[(i.setWidth 64).toNat]'hi_ws2' :=
                    Option.some.inj (by simp only [← List.getElem?_eq_getElem, hws25])
                  have hlhs_w : lhs = (s.scratch.work_stk2[(i.setWidth 64).toNat]'hi_ws2' &&&
                      ~~~1#32) ||| (1#32 ^^^ (neg_p &&& 1#32)) := by dsimp only [lhs]; rw [hwi]
                  have ⟨hcgr_eq, hpres_next, hseq_next⟩ := xorK_k35_post_ok (hmw := rfl) hmax4
                    hk3 hk5 hkcv hi_lt hcg_eq (by omega) hsc hscr5l hscrl_q htmpl_j htmpl_s
                    (by omega) (by rwa [← hws25]) (by rw [hws2l]; omega) hws2_lt hodd
                    hnp_par hlhs_w hpres5 hseq5 hpres_q hc hq_le hcov_q hperm_s
                    (by simpa [hcnt_eq, hj_eq] using hperm_j)
                  have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                  c0_hsteps!; refine ih5 (cur_g + 2#64 + (k - 1#32).setWidth 64, i + 1#32, ()) m5c
                    (by dsimp only; omega) ⟨by omega, by rw [hi1]; exact hcgr_eq,
                      { s5s with scratch := { s5s.scratch with scratch_buf := scr_q } },
                      (fidScr_lengthsOk
                        ⟨{ hl5.core_ok with tmp_len_arr := by rw [htmpl_s, htmpl_j] },
                          hs5hl.scratch_ok⟩ hscrl_q),
                      hc5, hs5, hmk5, hpres_next, hseq_next, hm5c⟩
            · have hi_eq5 : i.toNat = k.toNat := by omega
              c0_hsteps!; exact hQ cur_g s5 m5 hl5 hc5 hs5 hmk5 (by rw [hcg_eq, hi_eq5]; omega)
                (by rw [hcg_eq, hi_eq5]; omega) hpres5 hseq5 hm5

/-! ## 10. `full_cong_try_xor_ite_wp` (`Spec.fullCongTryXorIteSpec`) -/

/-- Canonical `Func.wp` proof for `full_cong_try_xor_ite`. -/
theorem full_cong_try_xor_ite_wp (Γ : Env)
    (hHasTern : Γ.Has "full_has_ternary" fullHasTernarySpec)
    (hEmitXor : Γ.Has "full_cong_emit_xor" Spec.fullCongEmitXorSpec) :
    ∀ args m Q X, Spec.fullCongTryXorIteSpec args m Q X →
      Func.wp Γ full_cong_try_xor_ite_body args m Q X := by
  rintro ⟨h, a, b, cl, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨maxA, c, F0, F_cur, s, R, hmax2, hmax64, rfl, hlen, hw, hnd, hcl0,
      ha_lt, hb_lt, hcl_lt, hab_ne, hac_ne, hbc_ne, hent0, hg5, hcap_bd, hseq0, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  let retNoop : ∀ m', (FullMem c s ⋆ R) m' → Q (g_len, ()) m' := fun m' hm' => by
    have h0 := hQ g_len s.scratch.scratch_buf m' hlen.scratch_ok.scratch_buf_len
      (Nat.le_refl _) (by omega) (fun _ _ => rfl) hseq0
    exact h0 (by simpa using hm')
  have hx1 : ∀ x : BitVec 32, (x ^^^ 1).toNat = x.toNat ^^^ 1 := fun x => by simp
  have hlt1_lit : ∀ x : BitVec 32, x.toNat < 2 * s.core.cur_vars →
      x.toNat ^^^ 1 < 2 * s.core.cur_vars := fun _ hx => litNeg_lt_two_mul hx
  have ha1_lt : (a ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [hx1]; exact hlt1_lit a ha_lt
  unfold Func.wp full_cong_try_xor_ite_body
  c0_hsplit
  · c0_hsteps!; exact retNoop m0 hm0
  clear hc; c0_hsplit
  · c0_hsteps!; exact retNoop m0 hm0
  clear hc; c0_hsplit
  · c0_hsteps!; exact retNoop m0 hm0
  clear hc; c0_hsteps_nogrp
  -- 5 nested `wp_join_group`s before the 3 `full_has_ternary` calls
  refine LeanQbe.T.wp_join_group (ts := [i32]) (fun _ m1 => m1 = m0) ?_ ?_
  · rintro _ ⟨_, ⟨⟩⟩ m1 hm1; c0_hsteps_nogrp
    refine LeanQbe.T.wp_join_group (ts := [i32]) (fun _ m2 => m2 = m0) ?_ ?_
    · rintro _ ⟨_, ⟨⟩⟩ m2 hm2; c0_hsteps_nogrp
      refine LeanQbe.T.wp_join_group (ts := []) (fun _ m3 => m3 = m0) ?_ ?_
      · rintro _ ⟨⟩ m3 hm3; c0_hsteps_nogrp
        refine LeanQbe.T.wp_join_group (ts := []) (fun _ m4 => m4 = m0) ?_ ?_
        · rintro _ ⟨⟩ m4 hm4; c0_hsteps_nogrp
          refine LeanQbe.T.wp_join_group (ts := []) (fun _ m5 => m5 = m0) ?_ ?_
          · rintro _ ⟨⟩ m5 hm5; c0_hsteps_nogrp
            have hne_bv : ∀ x y : BitVec 32, x.toNat / 2 ≠ y.toNat / 2 →
                x ≠ y ^^^ 1 ∧ x ^^^ 1 ≠ y ∧ x ^^^ 1 ≠ y ^^^ 1 := fun x y hxy =>
              ⟨fun h => hxy (by have t := congrArg BitVec.toNat h; rw [hx1] at t
                                rw [t]; exact (xor1_nat_xor1 y.toNat).1),
               fun h => hxy (by have t := congrArg BitVec.toNat h; rw [hx1] at t
                                rw [← t]; exact (xor1_nat_xor1 x.toNat).1.symm),
               fun h => hxy (by have t := congrArg (· / 2) (congrArg BitVec.toNat h)
                                rw [hx1, hx1] at t
                                rwa [(xor1_nat_xor1 x.toNat).1, (xor1_nat_xor1 y.toNat).1] at t)⟩
            have ⟨hne_ab1, hne_a1b, hne_a1b1⟩ := hne_bv a b hab_ne
            have ⟨hne_ac1, hne_a1c, hne_a1c1⟩ := hne_bv a cl hac_ne
            have ⟨hne_bc1, hne_b1c, hne_b1c1⟩ := hne_bv b cl hbc_ne
            refine wp_call_of_spec _ _ (hHasTern _ _ _ _ ⟨c, F0, F_cur, s, R, rfl, hlen, hw,
              hnd, hcl0, ha_lt, hm5 ▸ hm0, fun ok1 h1 => ?_⟩)
            c0_hsplit
            · have hc1 : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [a.toNat, b.toNat ^^^ 1, cl.toNat ^^^ 1]) := by
                have h' := h1 hc hne_ab1 hne_ac1 hne_b1c1
                change (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [a.toNat, (b ^^^ 1).toNat, (cl ^^^ 1).toNat]) at h'
                rwa [hx1, hx1] at h'
              clear hc; c0_hsteps_nogrp
              refine wp_call_of_spec _ _ (hHasTern _ _ _ _ ⟨c, F0, F_cur, s, R, rfl, hlen, hw,
                hnd, hcl0, ha1_lt, hm5 ▸ hm0, fun ok2 h2 => ?_⟩)
              c0_hsplit
              · have hc2 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [a.toNat ^^^ 1, b.toNat, cl.toNat ^^^ 1]) := by
                  have h' := h2 hc hne_a1b hne_a1c1 hne_bc1
                  change (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [(a ^^^ 1).toNat, b.toNat, (cl ^^^ 1).toNat]) at h'
                  rwa [hx1, hx1] at h'
                clear hc; c0_hsteps_nogrp
                refine wp_call_of_spec _ _ (hHasTern _ _ _ _ ⟨c, F0, F_cur, s, R, rfl, hlen, hw,
                  hnd, hcl0, ha1_lt, hm5 ▸ hm0, fun ok3 h3 => ?_⟩)
                c0_hsplit
                · have hc3 : (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [a.toNat ^^^ 1, b.toNat ^^^ 1, cl.toNat]) := by
                    have h' := h3 hc hne_a1b1 hne_a1c hne_b1c
                    change (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [(a ^^^ 1).toNat, (b ^^^ 1).toNat, cl.toNat]) at h'
                    rwa [hx1, hx1] at h'
                  obtain ⟨xd1, xd2, xd3⟩ := xor1_tryIte_xorDefs hent0 hc1 hc2 hc3
                  clear hc; c0_hsteps_nogrp
                  refine LeanQbe.T.wp_join_group (ts := [i64])
                    (fun (ret, ()) mf => ∃ scr' : List (BitVec 32),
                      scr'.length = c.scratch_cap ∧
                      g_len.toNat ≤ ret.toNat ∧ ret.toNat ≤ g_cap.toNat ∧
                      (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) ∧
                      CongGateSeqOk maxA F_cur s.core.cur_vars scr' ret.toNat 0 ∧
                      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr' } }
                        ⋆ R) mf) ?_ ?_
                  · rintro _ ⟨ret, ⟨⟩⟩ mf ⟨scr', hlen', hg_lo, hg_hi, hpres, hseq', hm_f⟩
                    c0_hsteps!; exact hQ ret scr' mf hlen' hg_lo hg_hi hpres hseq' hm_f
                  · intro Jend hJend
                    c0_hsplit
                    · have hle12 : g_len.toNat + 12 ≤ g_cap.toNat := by
                        have hle : ¬ g_cap.toNat < (g_len.toNat + 12) % 2 ^ 64 := by
                          simpa using hc
                        rw [Nat.mod_eq_of_lt (by omega)] at hle; omega
                      clear hc
                      have hscr0 := focus_full_scratch_buf (hm5 ▸ hm0)
                      have hcv2 : 2 ≤ s.core.cur_vars := by
                        by_cases hcv : 2 ≤ s.core.cur_vars; exact hcv
                        exfalso; have : s.core.cur_vars ≤ 1 := by omega
                        have ha0 : a.toNat / 2 = 0 := by omega
                        have hb0 : b.toNat / 2 = 0 := by omega
                        exact hab_ne (ha0.trans hb0.symm)
                      have hscr_len := hlen.scratch_ok.scratch_buf_len
                      refine wp_call_of_spec _ _ (hEmitXor _ _ _ _ ⟨maxA, F_cur, s.core.cur_vars,
                        s.scratch.scratch_buf, ArrayField.scratch_buf.rest c s ⋆ R,
                        hmax2, hmax64, ha_lt, hb_lt, hcl_lt, hcv2,
                        by change g_len.toNat + 4 ≤ s.scratch.scratch_buf.length; omega,
                        by omega,
                        xd1, hseq0, hscr0, fun scr1 m1 hl1 hp1 hseq1 hm1 => ?_⟩)
                      have hg4 : (g_len + 4#64).toNat = g_len.toNat + 4 := by bv_omega
                      have hp1' : ∀ idx < g_len.toNat, scr1[idx]? = s.scratch.scratch_buf[idx]? :=
                        hp1
                      have hseq1' : CongGateSeqOk maxA F_cur s.core.cur_vars scr1
                          (g_len.toNat + 4) 0 := hseq1
                      refine wp_call_of_spec _ _ (hEmitXor _ _ _ _ ⟨maxA, F_cur, s.core.cur_vars,
                        scr1, ArrayField.scratch_buf.rest c s ⋆ R,
                        hmax2, hmax64, hb_lt, ha_lt, hcl_lt, hcv2,
                        by change (g_len + 4#64).toNat + 4 ≤ scr1.length; omega,
                        by omega,
                        xd2, by rwa [← hg4] at hseq1', hm1, fun scr2 m2 hl2 hp2 hseq2 hm2 => ?_⟩)
                      have hg8 : (g_len + 4#64 + 4#64).toNat = g_len.toNat + 8 := by bv_omega
                      have hp2' : ∀ idx < (g_len + 4#64).toNat, scr2[idx]? = scr1[idx]? := hp2
                      have hseq2' : CongGateSeqOk maxA F_cur s.core.cur_vars scr2
                          ((g_len + 4#64).toNat + 4) 0 := hseq2
                      have hseq2'' : CongGateSeqOk maxA F_cur s.core.cur_vars scr2
                          (g_len + 4#64 + 4#64).toNat 0 := by
                        rw [hg4] at hseq2'
                        rwa [hg8, show g_len.toNat + 8 = g_len.toNat + 4 + 4 by omega]
                      refine wp_call_of_spec _ _ (hEmitXor _ _ _ _ ⟨maxA, F_cur, s.core.cur_vars,
                        scr2, ArrayField.scratch_buf.rest c s ⋆ R,
                        hmax2, hmax64, hcl_lt, ha_lt, hb_lt, hcv2,
                        by change (g_len + 4#64 + 4#64).toNat + 4 ≤ scr2.length; omega,
                        by omega,
                        xd3, hseq2'', hm2, fun scr3 m3 hl3 hp3 hseq3 hm3 => ?_⟩)
                      have hg12 : (g_len + 4#64 + 4#64 + 4#64).toNat = g_len.toNat + 12 := by
                        bv_omega
                      have hp3' : ∀ idx < (g_len + 4#64 + 4#64).toNat, scr3[idx]? = scr2[idx]? :=
                        hp3
                      have hseq3' : CongGateSeqOk maxA F_cur s.core.cur_vars scr3
                          ((g_len + 4#64 + 4#64).toNat + 4) 0 := hseq3
                      rw [hg8] at hseq3'
                      c0_hsteps!; exact hJend (g_len + 4#64 + 4#64 + 4#64, ()) m3 ⟨scr3, by omega,
                        by omega, by omega, fun idx hidx => by rw [hp3' idx (by rw [hg8]; omega),
                          hp2' idx (by rw [hg4]; omega), hp1' idx hidx],
                        by rwa [hg12, show g_len.toNat + 12 = g_len.toNat + 8 + 4 by omega],
                        unfocus_full_scratch_buf hm3⟩
                    · c0_hsteps!; exact hJend (g_len, ()) m5 ⟨s.scratch.scratch_buf,
                        hlen.scratch_ok.scratch_buf_len, Nat.le_refl _, by omega, fun _ _ => rfl,
                        hseq0, hm5 ▸ hm0⟩
                · c0_hsteps!; exact retNoop m5 (hm5 ▸ hm0)
              · c0_hsteps!; exact retNoop m5 (hm5 ▸ hm0)
            · c0_hsteps!; exact retNoop m5 (hm5 ▸ hm0)
          · intro J5 hJ5; c0_hsplit; · c0_hsteps!; exact hJ5 () m4 hm4
            clear hc; c0_hsplit; · c0_hsteps!; exact hJ5 () m4 hm4
            · c0_hsteps!; exact retNoop m4 (hm4 ▸ hm0)
        · intro J4 hJ4; c0_hsplit; · c0_hsteps!; exact hJ4 () m3 hm3
          clear hc; c0_hsplit; · c0_hsteps!; exact hJ4 () m3 hm3
          · c0_hsteps!; exact retNoop m3 (hm3 ▸ hm0)
      · intro J3 hJ3; c0_hsplit; · c0_hsteps!; exact hJ3 () m2 hm2
        clear hc; c0_hsplit; · c0_hsteps!; exact hJ3 () m2 hm2
        · c0_hsteps!; exact retNoop m2 (hm2 ▸ hm0)
    · intro J2 hJ2; c0_hsplit; · c0_hsteps!; exact hJ2 (_, ()) m1 hm1
      · c0_hsteps!; exact hJ2 (_, ()) m1 hm1
  · intro J1 hJ1; c0_hsplit; · c0_hsteps!; exact hJ1 (_, ()) m0 rfl
    · c0_hsteps!; exact hJ1 (_, ()) m0 rfl

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence

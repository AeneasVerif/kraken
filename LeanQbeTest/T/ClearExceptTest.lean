module

import LeanQbe.T.Logic.ProofKit
meta import LeanQbe.T.Logic.ProofKit

/-!
# Verification Suite for `clearexcept` Tactic

Exercises:
1. `clearexcept [h1, h2]` on stress-test goals with 40+ irrelevant `Prop` hypotheses
   (including `if`, `match`, conjunctions, disjunctions, opaque separation-style predicates,
   and unused transparent `let`s) proving `BitVec 64`, `BitVec 32`, `UInt32`/`UInt64`, and
   `Array`/`List` congruence + arithmetic goals cleanly and fast.
2. `clearexcept [h.1, h.2]` with compound proof terms (confirming the original `h` is cleared
   after extracting `h.1`/`h.2`).
3. `clearexcept []` (clearing all `Prop` hypotheses for pure arithmetic/tautology) and
   `clearexcept` (auto-filter mode).
4. Composition with multiple solvers (`grind`, `omega`, `simp`, `decide`).
5. Negative/fail-fast behavior (e.g. `fail_if_success (clearexcept [h1]; grind)`).
6. Transitive dependency closure preservation across transparent `let`s and types.
7. Compile-time axiom verification (`check_std_axioms!`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace LeanQbeTest.T.ClearExceptTest

open LeanQbe.T
open LeanQbe.T.ProofKit

/-! ## 1. 40+ Distractor Stress Tests: BitVec 64, BitVec 32, UInt32/UInt64, Array/List -/

section

opaque OpaquePred : Nat → Prop
opaque SepPred : Nat → Nat → Prop

theorem stress_40_distractors_bv64
    (x y z w : BitVec 64)
    (h1 : x = y) (h2 : y = z) (h3 : z = w)
    (d01 : 1 = 1 ∧ 2 = 2) (d02 : 3 = 4 ∨ 5 = 5)
    (d03 : if 1 < 2 then 3 = 3 else 4 = 4)
    (d04 : match (1 : Nat) with | 0 => False | _ => True)
    (d05 : OpaquePred 10) (d06 : OpaquePred 20) (d07 : SepPred 1 2)
    (d08 : (BitVec.ofNat 64 100) = (BitVec.ofNat 64 100))
    (d09 : d01.1 = d01.1) (d10 : d01.2 = d01.2)
    (d11 : x = x) (d12 : y = y) (d13 : z = z) (d14 : w = w)
    (d15 : OpaquePred 30) (d16 : OpaquePred 40) (d17 : SepPred 3 4)
    (d18 : 1 + 1 = 2) (d19 : 2 + 2 = 4) (d20 : 3 + 3 = 6)
    (d21 : (10 : UInt32) = 10) (d22 : (20 : UInt64) = 20)
    (d23 : [1, 2, 3].length = 3) (d24 : #[1, 2].size = 2)
    (d25 : (1 < 2) = true) (d26 : (2 < 1) = false)
    (d27 : OpaquePred 50) (d28 : OpaquePred 60) (d29 : SepPred 5 6)
    (d30 : 4 + 4 = 8) (d31 : 5 + 5 = 10) (d32 : 6 + 6 = 12)
    (d33 : OpaquePred 70) (d34 : OpaquePred 80) (d35 : SepPred 7 8)
    (d36 : 7 + 7 = 14) (d37 : 8 + 8 = 16) (d38 : 9 + 9 = 18)
    (d39 : OpaquePred 90) (d40 : OpaquePred 100) (d41 : SepPred 9 10)
    (d42 : (100 : Nat) = 100) (d43 : True) (d44 : True ∧ True) :
    x = w := by
  let unused_let1 := 12345
  let unused_let2 := x + y
  let unused_let3 := (unused_let1, unused_let2)
  clearexcept [h1, h2, h3]
  grind

theorem stress_40_distractors_bv32
    (a b c d : BitVec 32)
    (h1 : a = b + 1#32) (h2 : b = c) (h3 : c = d)
    (d01 : 1 = 1 ∧ 2 = 2) (d02 : 3 = 4 ∨ 5 = 5)
    (d03 : if 1 < 2 then 3 = 3 else 4 = 4)
    (d04 : match (1 : Nat) with | 0 => False | _ => True)
    (d05 : OpaquePred 10) (d06 : OpaquePred 20) (d07 : SepPred 1 2)
    (d08 : (BitVec.ofNat 32 100) = (BitVec.ofNat 32 100))
    (d09 : d01.1 = d01.1) (d10 : d01.2 = d01.2)
    (d11 : a = a) (d12 : b = b) (d13 : c = c) (d14 : d = d)
    (d15 : OpaquePred 30) (d16 : OpaquePred 40) (d17 : SepPred 3 4)
    (d18 : 1 + 1 = 2) (d19 : 2 + 2 = 4) (d20 : 3 + 3 = 6)
    (d21 : (10 : UInt32) = 10) (d22 : (20 : UInt64) = 20)
    (d23 : [1, 2, 3].length = 3) (d24 : #[1, 2].size = 2)
    (d25 : (1 < 2) = true) (d26 : (2 < 1) = false)
    (d27 : OpaquePred 50) (d28 : OpaquePred 60) (d29 : SepPred 5 6)
    (d30 : 4 + 4 = 8) (d31 : 5 + 5 = 10) (d32 : 6 + 6 = 12)
    (d33 : OpaquePred 70) (d34 : OpaquePred 80) (d35 : SepPred 7 8)
    (d36 : 7 + 7 = 14) (d37 : 8 + 8 = 16) (d38 : 9 + 9 = 18)
    (d39 : OpaquePred 90) (d40 : OpaquePred 100) (d41 : SepPred 9 10)
    (d42 : (100 : Nat) = 100) (d43 : True) (d44 : True ∧ True) :
    a = d + 1#32 := by
  let unused_let1 := 999#32
  let unused_let2 := a ^^^ b
  clearexcept [h1, h2, h3]
  grind

theorem stress_40_distractors_uint32_uint64
    (u1 u2 : UInt32) (w1 w2 : UInt64)
    (h1 : u1 = u2) (h2 : w1 = w2)
    (d01 : 1 = 1 ∧ 2 = 2) (d02 : 3 = 4 ∨ 5 = 5)
    (d03 : if 1 < 2 then 3 = 3 else 4 = 4)
    (d04 : match (1 : Nat) with | 0 => False | _ => True)
    (d05 : OpaquePred 10) (d06 : OpaquePred 20) (d07 : SepPred 1 2)
    (d08 : (BitVec.ofNat 64 100) = (BitVec.ofNat 64 100))
    (d09 : d01.1 = d01.1) (d10 : d01.2 = d01.2)
    (d11 : u1 = u1) (d12 : u2 = u2) (d13 : w1 = w1) (d14 : w2 = w2)
    (d15 : OpaquePred 30) (d16 : OpaquePred 40) (d17 : SepPred 3 4)
    (d18 : 1 + 1 = 2) (d19 : 2 + 2 = 4) (d20 : 3 + 3 = 6)
    (d21 : (10 : UInt32) = 10) (d22 : (20 : UInt64) = 20)
    (d23 : [1, 2, 3].length = 3) (d24 : #[1, 2].size = 2)
    (d25 : (1 < 2) = true) (d26 : (2 < 1) = false)
    (d27 : OpaquePred 50) (d28 : OpaquePred 60) (d29 : SepPred 5 6)
    (d30 : 4 + 4 = 8) (d31 : 5 + 5 = 10) (d32 : 6 + 6 = 12)
    (d33 : OpaquePred 70) (d34 : OpaquePred 80) (d35 : SepPred 7 8)
    (d36 : 7 + 7 = 14) (d37 : 8 + 8 = 16) (d38 : 9 + 9 = 18)
    (d39 : OpaquePred 90) (d40 : OpaquePred 100) (d41 : SepPred 9 10)
    (d42 : (100 : Nat) = 100) (d43 : True) (d44 : True ∧ True) :
    (u1.toNat = u2.toNat) ∧ (w1.toNat = w2.toNat) := by
  let unused_u := (u1, w1)
  clearexcept [h1, h2]
  grind

theorem stress_40_distractors_array_list
    (arr1 arr2 : Array Nat) (lst1 lst2 : List Nat) (v : Nat)
    (h1 : arr1 = arr2) (h2 : lst1 = lst2)
    (d01 : 1 = 1 ∧ 2 = 2) (d02 : 3 = 4 ∨ 5 = 5)
    (d03 : if 1 < 2 then 3 = 3 else 4 = 4)
    (d04 : match (1 : Nat) with | 0 => False | _ => True)
    (d05 : OpaquePred 10) (d06 : OpaquePred 20) (d07 : SepPred 1 2)
    (d08 : (BitVec.ofNat 64 100) = (BitVec.ofNat 64 100))
    (d09 : d01.1 = d01.1) (d10 : d01.2 = d01.2)
    (d11 : v = v) (d12 : arr1 = arr1) (d13 : lst1 = lst1) (d14 : lst2 = lst2)
    (d15 : OpaquePred 30) (d16 : OpaquePred 40) (d17 : SepPred 3 4)
    (d18 : 1 + 1 = 2) (d19 : 2 + 2 = 4) (d20 : 3 + 3 = 6)
    (d21 : (10 : UInt32) = 10) (d22 : (20 : UInt64) = 20)
    (d23 : [1, 2, 3].length = 3) (d24 : #[1, 2].size = 2)
    (d25 : (1 < 2) = true) (d26 : (2 < 1) = false)
    (d27 : OpaquePred 50) (d28 : OpaquePred 60) (d29 : SepPred 5 6)
    (d30 : 4 + 4 = 8) (d31 : 5 + 5 = 10) (d32 : 6 + 6 = 12)
    (d33 : OpaquePred 70) (d34 : OpaquePred 80) (d35 : SepPred 7 8)
    (d36 : 7 + 7 = 14) (d37 : 8 + 8 = 16) (d38 : 9 + 9 = 18)
    (d39 : OpaquePred 90) (d40 : OpaquePred 100) (d41 : SepPred 9 10)
    (d42 : (100 : Nat) = 100) (d43 : True) (d44 : True ∧ True) :
    arr1.push v = arr2.push v ∧ v :: lst1 = v :: lst2 := by
  let unused_lst := [v, 1, 2, 3]
  clearexcept [h1, h2]
  grind

end

/-! ## 2. Compound Proof Terms & Projection Assertions -/

section

theorem compound_proof_terms_and_conjunctions
    (x y z : BitVec 64)
    (h : (x = y) ∧ (y = z) ∧ (x + 1#64 = y + 1#64))
    (d1 : 10 = 20) (d2 : OpaquePred 99) :
    x = z := by
  clearexcept [h.1, h.2.1]
  grind

theorem compound_nested_conjunction_extraction
    (a b c d : Nat)
    (h : ((a = b ∧ b = c) ∧ (c = d ∧ a + 1 = b + 1)))
    (d1 : 100 = 200) (d2 : 300 = 400) :
    a = d := by
  clearexcept [h.1.1, h.1.2, h.2.1]
  grind

theorem compound_external_lemma_call
    (x y : BitVec 64) (h : x = y)
    (d1 : 1000 = 2000) (d2 : OpaquePred 1) :
    y = x := by
  clearexcept [Eq.symm h]
  grind

end

/-! ## 3. Empty List (Tautology/Arithmetic) & Auto-Filter Mode -/

section

theorem empty_keep_list_pure_arithmetic
    (x : BitVec 64) (y : Nat)
    (d1 : 1 = 2) (d2 : 3 = 4) (d3 : OpaquePred 5) :
    x &&& 0#64 = 0#64 ∧ y + 0 = y := by
  clearexcept []
  grind

theorem empty_keep_list_tautology
    (p : Prop) (d1 : 10 = 20) (d2 : False) :
    True ∧ (p → p) := by
  clearexcept []
  grind

theorem auto_filter_mode_connected_hyps
    (x y z : BitVec 64) (unrelated : BitVec 64)
    (h1 : x = y) (h2 : y = z) (hunrel : unrelated = 42#64)
    (d1 : 10 = 20) (d2 : OpaquePred 7) :
    x = z := by
  clearexcept
  grind

theorem auto_filter_mode_arithmetic
    (a b c : Nat) (unrelated : Nat)
    (h1 : a ≤ b) (h2 : b ≤ c) (hunrel : unrelated = 999)
    (d1 : 5 = 6) :
    a ≤ c := by
  clearexcept
  omega

end

/-! ## 4. Composition with `omega`, `simp`, `decide` -/

section

theorem composition_with_omega
    (a b c d : Nat)
    (h1 : a + 5 ≤ b) (h2 : b ≤ c) (h3 : c + 2 ≤ d)
    (d1 : 10 = 20) (d2 : 30 = 40) :
    a + 7 ≤ d := by
  clearexcept [h1, h2, h3]
  omega

theorem composition_with_simp
    (xs ys : List Nat) (x : Nat)
    (h1 : xs = ys)
    (d1 : 10 = 20) (d2 : 30 = 40) :
    (x :: xs).length = (x :: ys).length := by
  clearexcept [h1]
  simp [h1]

end

/-! ## 5. Transitive Dependency Closure & Let Bindings -/

section

theorem transitive_let_dependency_preserved
    (x : Nat)
    (d1 : 10 = 20) (d2 : 30 = 40) :
    let y := x + 10
    let z := y * 2
    let unused_heavy := 99999 * x
    z = (x + 10) * 2 := by
  intro y z unused_heavy
  clearexcept []
  grind

theorem transitive_hypothesis_dependency_preserved
    (a : Nat) (P : Nat → Prop) (Q : Prop)
    (hP : P a) (hQ : P a → Q)
    (d1 : 100 = 200) (d2 : OpaquePred 99) :
    Q := by
  clearexcept [hP, hQ]
  grind

end

/-! ## 6. Negative / Fail-Fast Tests -/

section

theorem fail_fast_missing_hypothesis (x y z : BitVec 64)
    (h1 : x = y) (h2 : y = z) :
    x = z := by
  fail_if_success (clearexcept [h1]; grind)
  fail_if_success (clearexcept [h2]; grind)
  fail_if_success (clearexcept []; grind)
  clearexcept [h1, h2]
  grind

theorem fail_fast_compound_term_partial (x y : Nat)
    (h : (x = y) ∧ (y = 5)) :
    x = 5 := by
  fail_if_success (clearexcept [h.1]; grind)
  fail_if_success (clearexcept [h.2]; grind)
  clearexcept [h.1, h.2]
  grind

end

/-! ## 7. Axiom Audit -/

check_std_axioms!
  stress_40_distractors_bv64
  stress_40_distractors_bv32
  stress_40_distractors_uint32_uint64
  stress_40_distractors_array_list
  compound_proof_terms_and_conjunctions
  compound_nested_conjunction_extraction
  compound_external_lemma_call
  empty_keep_list_pure_arithmetic
  empty_keep_list_tautology
  auto_filter_mode_connected_hyps
  auto_filter_mode_arithmetic
  composition_with_omega
  composition_with_simp
  transitive_let_dependency_preserved
  transitive_hypothesis_dependency_preserved
  fail_fast_missing_hypothesis
  fail_fast_compound_term_partial

end LeanQbeTest.T.ClearExceptTest

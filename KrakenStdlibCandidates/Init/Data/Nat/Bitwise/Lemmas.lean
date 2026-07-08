prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import KrakenStdlibCandidates.Init.Data.BitVec.Basic
import Lean


/-!
# Grind homomorphism and bitwise lemmas for Nat.
-/

open Lean Meta
set_option autoImplicit true

namespace Nat

attribute [grind_homo_pred] Nat.and_le_right


-- attribute [grind_homo_pred] Nat.shiftRight_le

attribute [ext] Nat.eq_of_testBit_eq
theorem land_mask_eq_mod (a m : Nat) (h : (m &&& (m + 1)) = 0) : a &&& m = a % (m + 1) := by
  have ⟨k, hk⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (
    by omega : m + 1 ≠ 0)).mp (by rw [Nat.add_sub_cancel, Nat.and_comm]; exact h)
  rw [hk, show m = 2^k - 1 by omega]
  exact Nat.and_two_pow_sub_one_eq_mod a k

theorem xor_two_pow_sub_one (x n : Nat) (h : x < 2^n) : x ^^^ (2^n - 1) = 2^n - 1 - x := by
  have h1 : x = (BitVec.ofNat n x).toNat :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  rw [h1, ← BitVec.toNat_allOnes, ← BitVec.toNat_xor, BitVec.xor_allOnes, BitVec.toNat_not, BitVec.toNat_allOnes, ← h1]

theorem submask_xor_eq_sub (a m : Nat) (h : m &&& (m + 1) = 0) : m ^^^ (a &&& m) = m - (a &&& m) := by
  have ⟨k, hk⟩ : (m+1).isPowerOfTwo := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (
    by omega)).mp (by rw [show _ - 1 = m by omega,  Nat.and_comm]; exact h)
  have hm : m = 2^k - 1 := by omega
  rw [hm, Nat.xor_comm, Nat.xor_two_pow_sub_one]
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt a (Nat.two_pow_pos k)

theorem testBit_two_pow_sub (k n i : Nat) (h_le : n ≤ k) :
  Nat.testBit (2^k - 2^n) i = (decide (n ≤ i) && decide (i < k)) := by
  have : 2^k - 2^n = (2^(k - n) - 1) * 2^n := by
    rw [Nat.mul_sub_right_distrib, Nat.one_mul, ← Nat.pow_add]
    congr 2; omega
  rw [this, Nat.testBit_mul_two_pow]
  by_cases h : n ≤ i <;> simp [h] <;> omega

theorem land_mask_eq_mod_shift (a k n : Nat) (h_le : n ≤ k) : a &&& (2^k - 2^n) = ((a >>> n) % 2^(k-n)) <<< n := by
  ext i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub _ _ _ h_le, Nat.testBit_shiftLeft]
  by_cases h_ni : n ≤ i
  · have e1 : i - n < k - n ↔ i < k := by omega
    have e2 : n + (i - n) = i := by omega
    simp [h_ni, e1, e2, Bool.and_comm]
  · simp [h_ni]

theorem neg_land_mask_eq_mod_shift (a k n : Nat) (h_le : n ≤ k) : (2^k - 2^n) ^^^ (a &&& (2^k - 2^n)) = ((2^(k-n) - 1 - ((a >>> n) % 2^(k-n)))) <<< n := by
  ext i
  rw [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub _ _ _ h_le]
  by_cases h_ni : n ≤ i <;> simp [h_ni]
  rw [show _ - 1 - ((a >>> n) % 2^(k-n)) = 2^(k-n) - (((a >>> n) % 2^(k-n)) + 1)
 by omega,  Nat.testBit_two_pow_sub_succ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  have h_iff : i - n < k - n ↔ i < k := by omega
  have h_eq : n + (i - n) = i := by omega
  simp [h_iff, h_eq]
  cases decide (i < k) <;> cases a.testBit i <;> rfl

theorem or_mod_two (a b : Nat) : (a ||| b) % 2 = (a % 2 ||| b % 2) := by
  have h : (a ||| b) % 2 = 1 ↔ a % 2 = 1 ∨ b % 2 = 1 := Nat.or_mod_two_eq_one
  have hab := Nat.mod_two_eq_zero_or_one (a ||| b)
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  simp [ha, hb] at * <;> omega

theorem and_mod_two (a b : Nat) : (a &&& b) % 2 = (a % 2 &&& b % 2) := by
  have h := Nat.and_mod_two_eq_one (a:=a) (b:=b)
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;> rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> rcases Nat.mod_two_eq_zero_or_one (a &&& b) with h3 | h3 <;> simp [h1, h2, h3] at h ⊢ <;> omega

theorem xor_mod_two (a b : Nat) : (a ^^^ b) % 2 = (a % 2 ^^^ b % 2) := by
  have := Nat.xor_mod_two_eq_one (a := a) (b := b)
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one (a ^^^ b) with h | h <;>
  simp [*] at *

theorem lor_add_land (a b : Nat) : (a ||| b) + (a &&& b) = a + b := by
  if h : a + b = 0 then
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rfl
  else
    have ih := lor_add_land (a / 2) (b / 2)
    have hm : (a % 2 ||| b % 2) + (a % 2 &&& b % 2) = a % 2 + b % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with hA | hA <;>
        rcases Nat.mod_two_eq_zero_or_one b with hB | hB <;> simp [hA, hB]
    have e1 : a ||| b = 2 * (a / 2 ||| b / 2) + (a % 2 ||| b % 2) := by
      rw [← Nat.or_div_two, ← Nat.or_mod_two]; exact (Nat.div_add_mod _ 2).symm
    have e2 : a &&& b = 2 * (a / 2 &&& b / 2) + (a % 2 &&& b % 2) := by
      rw [← Nat.and_div_two, ← Nat.and_mod_two]; exact (Nat.div_add_mod _ 2).symm
    omega
termination_by a + b

theorem xor_add_land (a b : Nat) : (a ^^^ b) + (a &&& b) = a ||| b := by
  if h : a + b = 0 then
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rfl
  else
    have ih := Nat.xor_add_land (a / 2) (b / 2)
    rw [← Nat.div_add_mod (a ^^^ b) 2, ← Nat.div_add_mod (a &&& b) 2, ← Nat.div_add_mod (a ||| b) 2]
    rw [Nat.xor_div_two, Nat.xor_mod_two, Nat.and_div_two, Nat.and_mod_two, Nat.or_div_two, Nat.or_mod_two]
    rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;> rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;>
    (rw [h1, h2]; dsimp; omega)
termination_by a + b

theorem xor_and_add_self_left (a b : Nat) : (a ^^^ (a &&& b)) + (a &&& b) = a := by
  have h_xor := Nat.xor_add_land a (a &&& b)
  have and_assoc_self (a b : Nat) : a &&& (a &&& b) = a &&& b := by
    ext i; grind
  have or_and_absorption (a b : Nat) : a ||| (a &&& b) = a := by
    ext i; grind
  rw [and_assoc_self, or_and_absorption] at h_xor
  exact h_xor

theorem xor_and_add_self_right (a b : Nat) : (b ^^^ (a &&& b)) + (a &&& b) = b := by
  have h_xor := Nat.xor_add_land b (a &&& b)
  have h_or : b ||| (a &&& b) = b := by
    ext i; grind
  have and_comm_assoc_self (a b : Nat) : b &&& (a &&& b) = a &&& b := by
    ext i; grind
  rw [and_comm_assoc_self, h_or] at h_xor
  exact h_xor

theorem xor_and_disjoint (a b : Nat) : (a ^^^ (a &&& b)) &&& (b ^^^ (a &&& b)) = 0 := by
  ext i; grind

theorem xor_and_or (a b : Nat) : (a ^^^ (a &&& b)) ||| (b ^^^ (a &&& b)) = a ^^^ b := by
  ext i; grind

theorem xor_and_add_xor (a b : Nat) : (a ^^^ (a &&& b)) + (b ^^^ (a &&& b)) = a ^^^ b := by
  have h := Nat.lor_add_land (a ^^^ (a &&& b)) (b ^^^ (a &&& b))
  rw [Nat.xor_and_or, Nat.xor_and_disjoint] at h
  lia

theorem rotateLeft_nat_eq (w x n : Nat) (hw : 0 < w) (hx : x < 2 ^ w) :
  let i := n % w
  (x <<< i % 2 ^ w) ||| (x >>> (w - i)) = (x * 2 ^ i + x / 2 ^ (w - i)) % 2 ^ w := by
  intro i
  have hi : i ≤ w := Nat.le_of_lt (Nat.mod_lt n hw)
  have hb : x >>> (w - i) < 2 ^ i := by
    rw [Nat.shiftRight_eq_div_pow]
    have h_pow : 2 ^ w = 2 ^ (w - i) * 2 ^ i :=
      by rw [← Nat.pow_add, Nat.sub_add_cancel hi]
    exact Nat.div_lt_of_lt_mul (h_pow ▸ hx)
  rw [← Nat.shiftLeft_eq, ← Nat.shiftRight_eq_div_pow]
  rw [Nat.shiftLeft_add_eq_or_of_lt hb]
  ext j
  simp [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hj : j < w
  · simp [hj]
  · simp [hj]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (
      by decide) (by omega)))

@[grind_homo]
theorem testBit_toBitVec n w i (h : n < 2^w) : n.testBit i = (BitVec.ofNat w n).getLsbD i := by
  simp [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

attribute [grind_homo] Nat.testBit_and
attribute [grind_homo] Nat.testBit_or
attribute [grind_homo] Nat.testBit_xor
attribute [grind_homo] Nat.testBit_shiftLeft
attribute [grind_homo] Nat.testBit_shiftRight
attribute [grind_homo] Nat.zero_testBit
attribute [grind_homo] Nat.testBit_one_eq_true_iff_self_eq_zero
attribute [grind_homo] Nat.testBit_two_pow_sub_one
attribute [grind_homo] Nat.testBit_mod_two_pow
attribute [grind_homo] Nat.testBit_two_pow_mul
attribute [grind_homo] Nat.testBit_two_pow_mul_add

end Nat

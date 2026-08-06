import Std

namespace Kraken.Examples

/-- Unsigned summation modulo `2^64`, matching C's `uint64_t` arithmetic. -/
def sumToN : Nat → UInt64
  | 0 => 0
  | n + 1 => UInt64.ofNat (n + 1) + sumToN n

theorem uint64_ofNat_succ_sub_one (n : Nat) (h : n + 1 < 2 ^ 64) :
    UInt64.ofNat (n + 1) - 1 = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_sub, UInt64.toNat_ofNat,
    UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt h]
  have hn : n < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hn]
  have hone : 1 % 2 ^ 64 = 1 := by decide
  rw [hone]
  have hadd : 2 ^ 64 - 1 + (n + 1) = 2 ^ 64 + n := by omega
  rw [hadd]
  simp [Nat.mod_eq_of_lt hn]

theorem uint64_ofNat_succ_beq_zero (n : Nat) (h : n + 1 < 2 ^ 64) :
    (UInt64.ofNat (n + 1) == 0) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq
  have hnat := congrArg UInt64.toNat heq
  simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat] at hnat
  rw [Nat.mod_eq_of_lt h] at hnat
  omega

end Kraken.Examples
